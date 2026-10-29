-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1648_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:12:34.398347+00:00
-- url     : https://prove2.me/submissions/0b0d4f36-84ce-4dd0-a606-c56b7cd8f2ed

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
theorem support_rectangle_w1648_s3_0 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-806537647/5000000000 : ℝ)*x 0 + (5448202771/10000000000 : ℝ)*x 1 + (647963617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (806537647/5000000000 : ℝ)^4911 ≤ (2493775815993/25000000000000 : ℝ)^3887 := by
    have hnat : (806537647 : ℕ)^4911*25000000000000^3887 ≤ 2493775815993^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806537647 5000000000 2493775815993 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5448202771/10000000000 : ℝ)^4911 ≤ (2901691569643/6250000000000 : ℝ)^3887 := by
    have hnat : (5448202771 : ℕ)^4911*6250000000000^3887 ≤ 2901691569643^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5448202771 10000000000 2901691569643 6250000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647963617/1250000000 : ℝ)^4911 ≤ (21798915803589/50000000000000 : ℝ)^3887 := by
    have hnat : (647963617 : ℕ)^4911*50000000000000^3887 ≤ 21798915803589^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647963617 1250000000 21798915803589 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-806537647/5000000000 : ℝ), (5448202771/10000000000 : ℝ), (647963617/1250000000 : ℝ)] ![(2493775815993/25000000000000 : ℝ), (2901691569643/6250000000000 : ℝ), (21798915803589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-806537647/5000000000 : ℝ)|^4911 ≤ (2493775815993/25000000000000 : ℝ)^3887
        have hw : |(-806537647/5000000000 : ℝ)|=(806537647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5448202771/10000000000 : ℝ)|^4911 ≤ (2901691569643/6250000000000 : ℝ)^3887
        have hw : |(5448202771/10000000000 : ℝ)|=(5448202771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647963617/1250000000 : ℝ)|^4911 ≤ (21798915803589/50000000000000 : ℝ)^3887
        have hw : |(647963617/1250000000 : ℝ)|=(647963617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s3_1 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267403267/500000000 : ℝ)*x 0 + (-874623567/5000000000 : ℝ)*x 1 + (2591854451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267403267/500000000 : ℝ)^4911 ≤ (9070312088493/20000000000000 : ℝ)^3887 := by
    have hnat : (267403267 : ℕ)^4911*20000000000000^3887 ≤ 9070312088493^3887*500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267403267 500000000 9070312088493 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (874623567/5000000000 : ℝ)^4911 ≤ (11050608294377/100000000000000 : ℝ)^3887 := by
    have hnat : (874623567 : ℕ)^4911*100000000000000^3887 ≤ 11050608294377^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874623567 5000000000 11050608294377 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591854451/5000000000 : ℝ)^4911 ≤ (21798915622943/50000000000000 : ℝ)^3887 := by
    have hnat : (2591854451 : ℕ)^4911*50000000000000^3887 ≤ 21798915622943^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591854451 5000000000 21798915622943 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267403267/500000000 : ℝ), (-874623567/5000000000 : ℝ), (2591854451/5000000000 : ℝ)] ![(9070312088493/20000000000000 : ℝ), (11050608294377/100000000000000 : ℝ), (21798915622943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267403267/500000000 : ℝ)|^4911 ≤ (9070312088493/20000000000000 : ℝ)^3887
        have hw : |(267403267/500000000 : ℝ)|=(267403267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-874623567/5000000000 : ℝ)|^4911 ≤ (11050608294377/100000000000000 : ℝ)^3887
        have hw : |(-874623567/5000000000 : ℝ)|=(874623567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591854451/5000000000 : ℝ)|^4911 ≤ (21798915622943/50000000000000 : ℝ)^3887
        have hw : |(2591854451/5000000000 : ℝ)|=(2591854451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s3_2 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337016329/2500000000 : ℝ)*x 0 + (2591854437/5000000000 : ℝ)*x 1 + (-1749247203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337016329/2500000000 : ℝ)^4911 ≤ (4535156018533/10000000000000 : ℝ)^3887 := by
    have hnat : (1337016329 : ℕ)^4911*10000000000000^3887 ≤ 4535156018533^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337016329 2500000000 4535156018533 10000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591854437/5000000000 : ℝ)^4911 ≤ (43597830948351/100000000000000 : ℝ)^3887 := by
    have hnat : (2591854437 : ℕ)^4911*100000000000000^3887 ≤ 43597830948351^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591854437 5000000000 43597830948351 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1749247203/10000000000 : ℝ)^4911 ≤ (2762652211277/25000000000000 : ℝ)^3887 := by
    have hnat : (1749247203 : ℕ)^4911*25000000000000^3887 ≤ 2762652211277^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749247203 10000000000 2762652211277 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337016329/2500000000 : ℝ), (2591854437/5000000000 : ℝ), (-1749247203/10000000000 : ℝ)] ![(4535156018533/10000000000000 : ℝ), (43597830948351/100000000000000 : ℝ), (2762652211277/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337016329/2500000000 : ℝ)|^4911 ≤ (4535156018533/10000000000000 : ℝ)^3887
        have hw : |(1337016329/2500000000 : ℝ)|=(1337016329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591854437/5000000000 : ℝ)|^4911 ≤ (43597830948351/100000000000000 : ℝ)^3887
        have hw : |(2591854437/5000000000 : ℝ)|=(2591854437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1749247203/10000000000 : ℝ)|^4911 ≤ (2762652211277/25000000000000 : ℝ)^3887
        have hw : |(-1749247203/10000000000 : ℝ)|=(1749247203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s3_3 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4182251981/10000000000 : ℝ)*x 0 + (48138587/125000000 : ℝ)*x 1 + (4533675289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182251981/10000000000 : ℝ)^4911 ≤ (4155120864991/12500000000000 : ℝ)^3887 := by
    have hnat : (4182251981 : ℕ)^4911*12500000000000^3887 ≤ 4155120864991^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182251981 10000000000 4155120864991 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (48138587/125000000 : ℝ)^4911 ≤ (29950802747193/100000000000000 : ℝ)^3887 := by
    have hnat : (48138587 : ℕ)^4911*100000000000000^3887 ≤ 29950802747193^3887*125000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48138587 125000000 29950802747193 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533675289/10000000000 : ℝ)^4911 ≤ (2300514394303/6250000000000 : ℝ)^3887 := by
    have hnat : (4533675289 : ℕ)^4911*6250000000000^3887 ≤ 2300514394303^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533675289 10000000000 2300514394303 6250000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182251981/10000000000 : ℝ), (48138587/125000000 : ℝ), (4533675289/10000000000 : ℝ)] ![(4155120864991/12500000000000 : ℝ), (29950802747193/100000000000000 : ℝ), (2300514394303/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182251981/10000000000 : ℝ)|^4911 ≤ (4155120864991/12500000000000 : ℝ)^3887
        have hw : |(4182251981/10000000000 : ℝ)|=(4182251981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(48138587/125000000 : ℝ)|^4911 ≤ (29950802747193/100000000000000 : ℝ)^3887
        have hw : |(48138587/125000000 : ℝ)|=(48138587/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533675289/10000000000 : ℝ)|^4911 ≤ (2300514394303/6250000000000 : ℝ)^3887
        have hw : |(4533675289/10000000000 : ℝ)|=(4533675289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s3_4 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1613140011/10000000000 : ℝ)*x 0 + (2592854983/5000000000 : ℝ)*x 1 + (5446180641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1613140011/10000000000 : ℝ)^4911 ≤ (9975608900949/100000000000000 : ℝ)^3887 := by
    have hnat : (1613140011 : ℕ)^4911*100000000000000^3887 ≤ 9975608900949^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613140011 10000000000 9975608900949 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592854983/5000000000 : ℝ)^4911 ≤ (43619096115967/100000000000000 : ℝ)^3887 := by
    have hnat : (2592854983 : ℕ)^4911*100000000000000^3887 ≤ 43619096115967^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592854983 5000000000 43619096115967 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5446180641/10000000000 : ℝ)^4911 ≤ (9281058995087/20000000000000 : ℝ)^3887 := by
    have hnat : (5446180641 : ℕ)^4911*20000000000000^3887 ≤ 9281058995087^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446180641 10000000000 9281058995087 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1613140011/10000000000 : ℝ), (2592854983/5000000000 : ℝ), (5446180641/10000000000 : ℝ)] ![(9975608900949/100000000000000 : ℝ), (43619096115967/100000000000000 : ℝ), (9281058995087/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1613140011/10000000000 : ℝ)|^4911 ≤ (9975608900949/100000000000000 : ℝ)^3887
        have hw : |(-1613140011/10000000000 : ℝ)|=(1613140011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592854983/5000000000 : ℝ)|^4911 ≤ (43619096115967/100000000000000 : ℝ)^3887
        have hw : |(2592854983/5000000000 : ℝ)|=(2592854983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5446180641/10000000000 : ℝ)|^4911 ≤ (9281058995087/20000000000000 : ℝ)^3887
        have hw : |(5446180641/10000000000 : ℝ)|=(5446180641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s3_5 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277421399/10000000000 : ℝ)*x 0 + (-297355081/2000000000 : ℝ)*x 1 + (108923613/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277421399/10000000000 : ℝ)^4911 ≤ (22298001863259/50000000000000 : ℝ)^3887 := by
    have hnat : (5277421399 : ℕ)^4911*50000000000000^3887 ≤ 22298001863259^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277421399 10000000000 22298001863259 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297355081/2000000000 : ℝ)^4911 ≤ (4499350595733/50000000000000 : ℝ)^3887 := by
    have hnat : (297355081 : ℕ)^4911*50000000000000^3887 ≤ 4499350595733^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297355081 2000000000 4499350595733 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108923613/200000000 : ℝ)^4911 ≤ (11601323768081/25000000000000 : ℝ)^3887 := by
    have hnat : (108923613 : ℕ)^4911*25000000000000^3887 ≤ 11601323768081^3887*200000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108923613 200000000 11601323768081 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277421399/10000000000 : ℝ), (-297355081/2000000000 : ℝ), (108923613/200000000 : ℝ)] ![(22298001863259/50000000000000 : ℝ), (4499350595733/50000000000000 : ℝ), (11601323768081/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277421399/10000000000 : ℝ)|^4911 ≤ (22298001863259/50000000000000 : ℝ)^3887
        have hw : |(5277421399/10000000000 : ℝ)|=(5277421399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297355081/2000000000 : ℝ)|^4911 ≤ (4499350595733/50000000000000 : ℝ)^3887
        have hw : |(-297355081/2000000000 : ℝ)|=(297355081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108923613/200000000 : ℝ)|^4911 ≤ (11601323768081/25000000000000 : ℝ)^3887
        have hw : |(108923613/200000000 : ℝ)|=(108923613/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s3_6 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277421397/10000000000 : ℝ)*x 0 + (5446180661/10000000000 : ℝ)*x 1 + (-46461731/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277421397/10000000000 : ℝ)^4911 ≤ (8919200741033/20000000000000 : ℝ)^3887 := by
    have hnat : (5277421397 : ℕ)^4911*20000000000000^3887 ≤ 8919200741033^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277421397 10000000000 8919200741033 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446180661/10000000000 : ℝ)^4911 ≤ (46405295190743/100000000000000 : ℝ)^3887 := by
    have hnat : (5446180661 : ℕ)^4911*100000000000000^3887 ≤ 46405295190743^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446180661 10000000000 46405295190743 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (46461731/312500000 : ℝ)^4911 ≤ (1799740218411/20000000000000 : ℝ)^3887 := by
    have hnat : (46461731 : ℕ)^4911*20000000000000^3887 ≤ 1799740218411^3887*312500000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46461731 312500000 1799740218411 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277421397/10000000000 : ℝ), (5446180661/10000000000 : ℝ), (-46461731/312500000 : ℝ)] ![(8919200741033/20000000000000 : ℝ), (46405295190743/100000000000000 : ℝ), (1799740218411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277421397/10000000000 : ℝ)|^4911 ≤ (8919200741033/20000000000000 : ℝ)^3887
        have hw : |(5277421397/10000000000 : ℝ)|=(5277421397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446180661/10000000000 : ℝ)|^4911 ≤ (46405295190743/100000000000000 : ℝ)^3887
        have hw : |(5446180661/10000000000 : ℝ)|=(5446180661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-46461731/312500000 : ℝ)|^4911 ≤ (1799740218411/20000000000000 : ℝ)^3887
        have hw : |(-46461731/312500000 : ℝ)|=(46461731/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s3_7 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836483803/2000000000 : ℝ)*x 0 + (905702207/2000000000 : ℝ)*x 1 + (3856305611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836483803/2000000000 : ℝ)^4911 ≤ (6648528855777/20000000000000 : ℝ)^3887 := by
    have hnat : (836483803 : ℕ)^4911*20000000000000^3887 ≤ 6648528855777^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836483803 2000000000 6648528855777 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (905702207/2000000000 : ℝ)^4911 ≤ (459440811251/1250000000000 : ℝ)^3887 := by
    have hnat : (905702207 : ℕ)^4911*1250000000000^3887 ≤ 459440811251^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      905702207 2000000000 459440811251 1250000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3856305611/10000000000 : ℝ)^4911 ≤ (3750261350969/12500000000000 : ℝ)^3887 := by
    have hnat : (3856305611 : ℕ)^4911*12500000000000^3887 ≤ 3750261350969^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3856305611 10000000000 3750261350969 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836483803/2000000000 : ℝ), (905702207/2000000000 : ℝ), (3856305611/10000000000 : ℝ)] ![(6648528855777/20000000000000 : ℝ), (459440811251/1250000000000 : ℝ), (3750261350969/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836483803/2000000000 : ℝ)|^4911 ≤ (6648528855777/20000000000000 : ℝ)^3887
        have hw : |(836483803/2000000000 : ℝ)|=(836483803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(905702207/2000000000 : ℝ)|^4911 ≤ (459440811251/1250000000000 : ℝ)^3887
        have hw : |(905702207/2000000000 : ℝ)|=(905702207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3856305611/10000000000 : ℝ)|^4911 ≤ (3750261350969/12500000000000 : ℝ)^3887
        have hw : |(3856305611/10000000000 : ℝ)|=(3856305611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1648_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2131/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16277/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2647/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (511/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2647/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2647/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (511/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2647/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2647/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (511/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2647/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2647/25000 : ℝ) ^ (4907/1024 : ℝ) ≤ (1061416875321733/50000000000000000000 : ℝ) := by
    have hpowers : (2647/25000 : ℝ)^4907 ≤ (1061416875321733/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2647 : ℕ)^4907*50000000000000000000^1024 ≤ 1061416875321733^1024*25000^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2647 25000 1061416875321733 50000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2647/25000 : ℝ)) (X := (1061416875321733/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (511/3125 : ℝ) ^ (4907/1024 : ℝ) ≤ (1703875246096563/10000000000000000000 : ℝ) := by
    have hpowers : (511/3125 : ℝ)^4907 ≤ (1703875246096563/10000000000000000000 : ℝ)^1024 := by
      have hnat : (511 : ℕ)^4907*10000000000000000000^1024 ≤ 1703875246096563^1024*3125^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        511 3125 1703875246096563 10000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (511/3125 : ℝ)) (X := (1703875246096563/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001061416875321733/25000000000000000000 : ℝ) ≤ (2500022149431889/2500000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (25001061416875321733/25000000000000000000 : ℝ)^1024 ≤ (2500022149431889/2500000000000000 : ℝ)^4907 := by
      have hnat : (25001061416875321733 : ℕ)^1024*2500000000000000^4907 ≤ 2500022149431889^4907*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001061416875321733 25000000000000000000 2500022149431889 2500000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500022149431889/2500000000000000 : ℝ)) (X := (25001061416875321733/25000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502395198276451137/12500000000000000000 : ℝ) ≤ (10000399836495977/10000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (12502395198276451137/12500000000000000000 : ℝ)^1024 ≤ (10000399836495977/10000000000000000 : ℝ)^4907 := by
      have hnat : (12502395198276451137 : ℕ)^1024*10000000000000000^4907 ≤ 10000399836495977^4907*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502395198276451137 12500000000000000000 10000399836495977 10000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000399836495977/10000000000000000 : ℝ)) (X := (12502395198276451137/12500000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5001703875246096563/5000000000000000000 : ℝ) ≤ (5000355537632199/5000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (5001703875246096563/5000000000000000000 : ℝ)^1024 ≤ (5000355537632199/5000000000000000 : ℝ)^4907 := by
      have hnat : (5001703875246096563 : ℕ)^1024*5000000000000000^4907 ≤ 5000355537632199^4907*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001703875246096563 5000000000000000000 5000355537632199 5000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000355537632199/5000000000000000 : ℝ)) (X := (5001703875246096563/5000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1061416875321733/50000000000000000000 : ℝ) ≤ ((7204239985642693711/7205000000000000000 : ℝ)+2*(311238768421/576400000000000 : ℝ)*(2647/25000 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (7204239985642693711/7205000000000000000 : ℝ)+2*(311238768421/576400000000000 : ℝ)*(2647/25000 : ℝ)=(2500022149431889/2500000000000000 : ℝ) by norm_num, show 1+2*(1061416875321733/50000000000000000000 : ℝ)=(25001061416875321733/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1703875246096563/10000000000000000000 : ℝ)+(1061416875321733/50000000000000000000 : ℝ) ≤ ((7204239985642693711/7205000000000000000 : ℝ)+(311238768421/576400000000000 : ℝ)*((511/3125 : ℝ)+(2647/25000 : ℝ)))^(4907/1024 : ℝ) := by
    rw [show (7204239985642693711/7205000000000000000 : ℝ)+(311238768421/576400000000000 : ℝ)*((511/3125 : ℝ)+(2647/25000 : ℝ))=(10000399836495977/10000000000000000 : ℝ) by norm_num, show 1+(1703875246096563/10000000000000000000 : ℝ)+(1061416875321733/50000000000000000000 : ℝ)=(12502395198276451137/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1703875246096563/10000000000000000000 : ℝ) ≤ ((7204239985642693711/7205000000000000000 : ℝ)+2*(311238768421/576400000000000 : ℝ)*(511/3125 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (7204239985642693711/7205000000000000000 : ℝ)+2*(311238768421/576400000000000 : ℝ)*(511/3125 : ℝ)=(5000355537632199/5000000000000000 : ℝ) by norm_num, show 1+2*(1703875246096563/10000000000000000000 : ℝ)=(5001703875246096563/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7204239985642693711/7205000000000000000 : ℝ)*(X 1 0+X 2 0)+(311238768421/576400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (7204239985642693711/7205000000000000000 : ℝ)) (alpha := (311238768421/576400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7204239985642693711/7205000000000000000 : ℝ)*(X 0 1+X 2 1)+(311238768421/576400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (7204239985642693711/7205000000000000000 : ℝ)) (alpha := (311238768421/576400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7204239985642693711/7205000000000000000 : ℝ)*(X 0 2+X 1 2)+(311238768421/576400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (2647/25000 : ℝ)) (hi := (511/3125 : ℝ)) (c := (7204239985642693711/7205000000000000000 : ℝ)) (alpha := (311238768421/576400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-806537647/5000000000 : ℝ)*X 0 0+(5448202771/10000000000 : ℝ)*X 0 1+(647963617/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267403267/500000000 : ℝ)*X 1 0+(-874623567/5000000000 : ℝ)*X 1 1+(2591854451/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337016329/2500000000 : ℝ)*X 2 0+(2591854437/5000000000 : ℝ)*X 2 1+(-1749247203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4182251981/10000000000 : ℝ)*X 0 0+(48138587/125000000 : ℝ)*X 0 1+(4533675289/10000000000 : ℝ)*X 0 2+(4182251981/10000000000 : ℝ)*X 1 0+(48138587/125000000 : ℝ)*X 1 1+(4533675289/10000000000 : ℝ)*X 1 2+(4182251981/10000000000 : ℝ)*X 2 0+(48138587/125000000 : ℝ)*X 2 1+(4533675289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1613140011/10000000000 : ℝ)*X 0 0+(2592854983/5000000000 : ℝ)*X 0 1+(5446180641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277421399/10000000000 : ℝ)*X 1 0+(-297355081/2000000000 : ℝ)*X 1 1+(108923613/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5277421397/10000000000 : ℝ)*X 2 0+(5446180661/10000000000 : ℝ)*X 2 1+(-46461731/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((836483803/2000000000 : ℝ)*X 0 0+(905702207/2000000000 : ℝ)*X 0 1+(3856305611/10000000000 : ℝ)*X 0 2+(836483803/2000000000 : ℝ)*X 1 0+(905702207/2000000000 : ℝ)*X 1 1+(3856305611/10000000000 : ℝ)*X 1 2+(836483803/2000000000 : ℝ)*X 2 0+(905702207/2000000000 : ℝ)*X 2 1+(3856305611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1037221597522062769651911039/90062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1808009829/100000000000000 : ℝ)*(base19) + (837961793/50000000000000 : ℝ)*(base23) + (15391637/25000000000000 : ℝ)*(lower2) + (306132837/100000000000000 : ℝ)*(upper3) + (83203841/50000000000000 : ℝ)*(upper5) + (1311470201050333/50000000000000 : ℝ)*(major0) + (1311470201050333/50000000000000 : ℝ)*(major1) + (2622940402100667/100000000000000 : ℝ)*(major2) + (1890414820402251/50000000000000 : ℝ)*(sp0) + (945212214026483/25000000000000 : ℝ)*(sp1) + (1890424494096087/50000000000000 : ℝ)*(sp2) + (732510036571917/50000000000000 : ℝ)*(sp3) + (21023311259/100000000000000 : ℝ)*(sp4) + (4841526087/50000000000000 : ℝ)*(sp7) + (183128719524501/12500000000000 : ℝ)*(f.failure) + (47260633301447/1250000000000 : ℝ)*(f.sum) + (17297335416913/57640000000000000000000000000 : ℝ)*base65 + (4747061988407900487/360250000000000000000000000000000 : ℝ)*base68 + (33363960289130237/720500000000000000000000000000000 : ℝ)*base69 + (2013915010907400487/360250000000000000000000000000000 : ℝ)*base72 + (48948640172313/57640000000000000000000000000 : ℝ)*base73 + (711517596157369763/720500000000000000000000000000000 : ℝ)*base76 + (940312300676031737/360250000000000000000000000000000 : ℝ)*base78 + (3667958165570531737/360250000000000000000000000000000 : ℝ)*base80 + (56206461895187/14410000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (38083/156250000000000000000 : ℝ)*base89 + (38083/156250000000000000000 : ℝ)*base91 + (1524417/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1714173105969379285823505729/180125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27895377/2000000000000 : ℝ)*(base19) + (379181867/25000000000000 : ℝ)*(base23) + (205926477/100000000000000 : ℝ)*(upper3) + (3329037/6250000000000 : ℝ)*(lower4) + (48215029/25000000000000 : ℝ)*(upper5) + (1331710839190671/50000000000000 : ℝ)*(major0) + (1331710839190671/50000000000000 : ℝ)*(major1) + (1331710839190671/50000000000000 : ℝ)*(major2) + (16484872981/100000000000000 : ℝ)*(sp1) + (9082281363/50000000000000 : ℝ)*(sp2) + (959800669115119/25000000000000 : ℝ)*(sp4) + (1919592398409323/50000000000000 : ℝ)*(sp5) + (1919591497585141/50000000000000 : ℝ)*(sp6) + (1487640363083029/100000000000000 : ℝ)*(sp7) + (1487640363083029/100000000000000 : ℝ)*(f.failure) + (959800669115119/25000000000000 : ℝ)*(f.sum) + (2619502422901/14410000000000000000000000000 : ℝ)*base65 + (1576411567280042419/360250000000000000000000000000000 : ℝ)*base68 + (1163994486721042419/360250000000000000000000000000000 : ℝ)*base70 + (3654676488534542419/360250000000000000000000000000000 : ℝ)*base72 + (14961008424781/14410000000000000000000000000 : ℝ)*base73 + (4968426012192542419/360250000000000000000000000000000 : ℝ)*base76 + (2069991163663542419/360250000000000000000000000000000 : ℝ)*base78 + (613767047657542419/360250000000000000000000000000000 : ℝ)*base80 + (47679160325721/14410000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (8396907/1250000000000000000000 : ℝ)*base89 + (8396907/1250000000000000000000 : ℝ)*base91 + (8396907/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1648_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1648_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1648_s4_0 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-403280671/2500000000 : ℝ)*x 0 + (2723981923/5000000000 : ℝ)*x 1 + (647989521/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (403280671/2500000000 : ℝ)^4911 ≤ (2493868380939/25000000000000 : ℝ)^3887 := by
    have hnat : (403280671 : ℕ)^4911*25000000000000^3887 ≤ 2493868380939^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403280671 2500000000 2493868380939 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2723981923/5000000000 : ℝ)^4911 ≤ (725382699221/1562500000000 : ℝ)^3887 := by
    have hnat : (2723981923 : ℕ)^4911*1562500000000^3887 ≤ 725382699221^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2723981923 5000000000 725382699221 1562500000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647989521/1250000000 : ℝ)^4911 ≤ (43600033716019/100000000000000 : ℝ)^3887 := by
    have hnat : (647989521 : ℕ)^4911*100000000000000^3887 ≤ 43600033716019^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647989521 1250000000 43600033716019 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-403280671/2500000000 : ℝ), (2723981923/5000000000 : ℝ), (647989521/1250000000 : ℝ)] ![(2493868380939/25000000000000 : ℝ), (725382699221/1562500000000 : ℝ), (43600033716019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-403280671/2500000000 : ℝ)|^4911 ≤ (2493868380939/25000000000000 : ℝ)^3887
        have hw : |(-403280671/2500000000 : ℝ)|=(403280671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2723981923/5000000000 : ℝ)|^4911 ≤ (725382699221/1562500000000 : ℝ)^3887
        have hw : |(2723981923/5000000000 : ℝ)|=(2723981923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647989521/1250000000 : ℝ)|^4911 ≤ (43600033716019/100000000000000 : ℝ)^3887
        have hw : |(647989521/1250000000 : ℝ)|=(647989521/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s4_1 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267400039/500000000 : ℝ)*x 0 + (-1749058047/10000000000 : ℝ)*x 1 + (5183916019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267400039/500000000 : ℝ)^4911 ≤ (45350868748869/100000000000000 : ℝ)^3887 := by
    have hnat : (267400039 : ℕ)^4911*100000000000000^3887 ≤ 45350868748869^3887*500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267400039 500000000 45350868748869 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1749058047/10000000000 : ℝ)^4911 ≤ (1104909909751/10000000000000 : ℝ)^3887 := by
    have hnat : (1749058047 : ℕ)^4911*10000000000000^3887 ≤ 1104909909751^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1749058047 10000000000 1104909909751 10000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183916019/10000000000 : ℝ)^4911 ≤ (10900008033173/25000000000000 : ℝ)^3887 := by
    have hnat : (5183916019 : ℕ)^4911*25000000000000^3887 ≤ 10900008033173^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183916019 10000000000 10900008033173 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267400039/500000000 : ℝ), (-1749058047/10000000000 : ℝ), (5183916019/10000000000 : ℝ)] ![(45350868748869/100000000000000 : ℝ), (1104909909751/10000000000000 : ℝ), (10900008033173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267400039/500000000 : ℝ)|^4911 ≤ (45350868748869/100000000000000 : ℝ)^3887
        have hw : |(267400039/500000000 : ℝ)|=(267400039/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1749058047/10000000000 : ℝ)|^4911 ≤ (1104909909751/10000000000000 : ℝ)^3887
        have hw : |(-1749058047/10000000000 : ℝ)|=(1749058047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183916019/10000000000 : ℝ)|^4911 ≤ (10900008033173/25000000000000 : ℝ)^3887
        have hw : |(5183916019/10000000000 : ℝ)|=(5183916019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s4_2 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213920029/400000000 : ℝ)*x 0 + (1295978969/2500000000 : ℝ)*x 1 + (-218632289/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213920029/400000000 : ℝ)^4911 ≤ (22675434079801/50000000000000 : ℝ)^3887 := by
    have hnat : (213920029 : ℕ)^4911*50000000000000^3887 ≤ 22675434079801^3887*400000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213920029 400000000 22675434079801 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295978969/2500000000 : ℝ)^4911 ≤ (10900007653281/25000000000000 : ℝ)^3887 := by
    have hnat : (1295978969 : ℕ)^4911*25000000000000^3887 ≤ 10900007653281^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295978969 2500000000 10900007653281 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218632289/1250000000 : ℝ)^4911 ≤ (345284412893/3125000000000 : ℝ)^3887 := by
    have hnat : (218632289 : ℕ)^4911*3125000000000^3887 ≤ 345284412893^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218632289 1250000000 345284412893 3125000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213920029/400000000 : ℝ), (1295978969/2500000000 : ℝ), (-218632289/1250000000 : ℝ)] ![(22675434079801/50000000000000 : ℝ), (10900007653281/25000000000000 : ℝ), (345284412893/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213920029/400000000 : ℝ)|^4911 ≤ (22675434079801/50000000000000 : ℝ)^3887
        have hw : |(213920029/400000000 : ℝ)|=(213920029/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295978969/2500000000 : ℝ)|^4911 ≤ (10900007653281/25000000000000 : ℝ)^3887
        have hw : |(1295978969/2500000000 : ℝ)|=(1295978969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-218632289/1250000000 : ℝ)|^4911 ≤ (345284412893/3125000000000 : ℝ)^3887
        have hw : |(-218632289/1250000000 : ℝ)|=(218632289/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s4_3 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261392677/625000000 : ℝ)*x 0 + (3851659037/10000000000 : ℝ)*x 1 + (4533097061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261392677/625000000 : ℝ)^4911 ≤ (33241276724993/100000000000000 : ℝ)^3887 := by
    have hnat : (261392677 : ℕ)^4911*100000000000000^3887 ≤ 33241276724993^3887*625000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261392677 625000000 33241276724993 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3851659037/10000000000 : ℝ)^4911 ≤ (29956424134647/100000000000000 : ℝ)^3887 := by
    have hnat : (3851659037 : ℕ)^4911*100000000000000^3887 ≤ 29956424134647^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3851659037 10000000000 29956424134647 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533097061/10000000000 : ℝ)^4911 ≤ (4600287390019/12500000000000 : ℝ)^3887 := by
    have hnat : (4533097061 : ℕ)^4911*12500000000000^3887 ≤ 4600287390019^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533097061 10000000000 4600287390019 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261392677/625000000 : ℝ), (3851659037/10000000000 : ℝ), (4533097061/10000000000 : ℝ)] ![(33241276724993/100000000000000 : ℝ), (29956424134647/100000000000000 : ℝ), (4600287390019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261392677/625000000 : ℝ)|^4911 ≤ (33241276724993/100000000000000 : ℝ)^3887
        have hw : |(261392677/625000000 : ℝ)|=(261392677/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3851659037/10000000000 : ℝ)|^4911 ≤ (29956424134647/100000000000000 : ℝ)^3887
        have hw : |(3851659037/10000000000 : ℝ)|=(3851659037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533097061/10000000000 : ℝ)|^4911 ≤ (4600287390019/12500000000000 : ℝ)^3887
        have hw : |(4533097061/10000000000 : ℝ)|=(4533097061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s4_4 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1613187181/10000000000 : ℝ)*x 0 + (1037182071/2000000000 : ℝ)*x 1 + (2722974293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1613187181/10000000000 : ℝ)^4911 ≤ (4987988722877/50000000000000 : ℝ)^3887 := by
    have hnat : (1613187181 : ℕ)^4911*50000000000000^3887 ≤ 4987988722877^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1613187181 10000000000 4987988722877 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037182071/2000000000 : ℝ)^4911 ≤ (21810612862599/50000000000000 : ℝ)^3887 := by
    have hnat : (1037182071 : ℕ)^4911*50000000000000^3887 ≤ 21810612862599^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037182071 2000000000 21810612862599 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722974293/5000000000 : ℝ)^4911 ≤ (46402796820429/100000000000000 : ℝ)^3887 := by
    have hnat : (2722974293 : ℕ)^4911*100000000000000^3887 ≤ 46402796820429^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722974293 5000000000 46402796820429 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1613187181/10000000000 : ℝ), (1037182071/2000000000 : ℝ), (2722974293/5000000000 : ℝ)] ![(4987988722877/50000000000000 : ℝ), (21810612862599/50000000000000 : ℝ), (46402796820429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1613187181/10000000000 : ℝ)|^4911 ≤ (4987988722877/50000000000000 : ℝ)^3887
        have hw : |(-1613187181/10000000000 : ℝ)|=(1613187181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037182071/2000000000 : ℝ)|^4911 ≤ (21810612862599/50000000000000 : ℝ)^3887
        have hw : |(1037182071/2000000000 : ℝ)|=(1037182071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722974293/5000000000 : ℝ)|^4911 ≤ (46402796820429/100000000000000 : ℝ)^3887
        have hw : |(2722974293/5000000000 : ℝ)|=(2722974293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s4_5 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638738003/5000000000 : ℝ)*x 0 + (-23234779/156250000 : ℝ)*x 1 + (2722974293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638738003/5000000000 : ℝ)^4911 ≤ (5574573342479/12500000000000 : ℝ)^3887 := by
    have hnat : (2638738003 : ℕ)^4911*12500000000000^3887 ≤ 5574573342479^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638738003 5000000000 5574573342479 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23234779/156250000 : ℝ)^4911 ≤ (2250154106829/25000000000000 : ℝ)^3887 := by
    have hnat : (23234779 : ℕ)^4911*25000000000000^3887 ≤ 2250154106829^3887*156250000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23234779 156250000 2250154106829 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2722974293/5000000000 : ℝ)^4911 ≤ (46402796820429/100000000000000 : ℝ)^3887 := by
    have hnat : (2722974293 : ℕ)^4911*100000000000000^3887 ≤ 46402796820429^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722974293 5000000000 46402796820429 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638738003/5000000000 : ℝ), (-23234779/156250000 : ℝ), (2722974293/5000000000 : ℝ)] ![(5574573342479/12500000000000 : ℝ), (2250154106829/25000000000000 : ℝ), (46402796820429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638738003/5000000000 : ℝ)|^4911 ≤ (5574573342479/12500000000000 : ℝ)^3887
        have hw : |(2638738003/5000000000 : ℝ)|=(2638738003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23234779/156250000 : ℝ)|^4911 ≤ (2250154106829/25000000000000 : ℝ)^3887
        have hw : |(-23234779/156250000 : ℝ)|=(23234779/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2722974293/5000000000 : ℝ)|^4911 ≤ (46402796820429/100000000000000 : ℝ)^3887
        have hw : |(2722974293/5000000000 : ℝ)|=(2722974293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s4_6 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638738003/5000000000 : ℝ)*x 0 + (2722974293/5000000000 : ℝ)*x 1 + (-23234779/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638738003/5000000000 : ℝ)^4911 ≤ (5574573342479/12500000000000 : ℝ)^3887 := by
    have hnat : (2638738003 : ℕ)^4911*12500000000000^3887 ≤ 5574573342479^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638738003 5000000000 5574573342479 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722974293/5000000000 : ℝ)^4911 ≤ (46402796820429/100000000000000 : ℝ)^3887 := by
    have hnat : (2722974293 : ℕ)^4911*100000000000000^3887 ≤ 46402796820429^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722974293 5000000000 46402796820429 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23234779/156250000 : ℝ)^4911 ≤ (2250154106829/25000000000000 : ℝ)^3887 := by
    have hnat : (23234779 : ℕ)^4911*25000000000000^3887 ≤ 2250154106829^3887*156250000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23234779 156250000 2250154106829 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638738003/5000000000 : ℝ), (2722974293/5000000000 : ℝ), (-23234779/156250000 : ℝ)] ![(5574573342479/12500000000000 : ℝ), (46402796820429/100000000000000 : ℝ), (2250154106829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638738003/5000000000 : ℝ)|^4911 ≤ (5574573342479/12500000000000 : ℝ)^3887
        have hw : |(2638738003/5000000000 : ℝ)|=(2638738003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722974293/5000000000 : ℝ)|^4911 ≤ (46402796820429/100000000000000 : ℝ)^3887
        have hw : |(2722974293/5000000000 : ℝ)|=(2722974293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23234779/156250000 : ℝ)|^4911 ≤ (2250154106829/25000000000000 : ℝ)^3887
        have hw : |(-23234779/156250000 : ℝ)|=(23234779/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_s4_7 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (836489827/2000000000 : ℝ)*x 0 + (4527949721/10000000000 : ℝ)*x 1 + (771372081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (836489827/2000000000 : ℝ)^4911 ≤ (33242946746439/100000000000000 : ℝ)^3887 := by
    have hnat : (836489827 : ℕ)^4911*100000000000000^3887 ≤ 33242946746439^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      836489827 2000000000 33242946746439 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4527949721/10000000000 : ℝ)^4911 ≤ (9187377233243/25000000000000 : ℝ)^3887 := by
    have hnat : (4527949721 : ℕ)^4911*25000000000000^3887 ≤ 9187377233243^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527949721 10000000000 9187377233243 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771372081/2000000000 : ℝ)^4911 ≤ (30007544309487/100000000000000 : ℝ)^3887 := by
    have hnat : (771372081 : ℕ)^4911*100000000000000^3887 ≤ 30007544309487^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771372081 2000000000 30007544309487 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(836489827/2000000000 : ℝ), (4527949721/10000000000 : ℝ), (771372081/2000000000 : ℝ)] ![(33242946746439/100000000000000 : ℝ), (9187377233243/25000000000000 : ℝ), (30007544309487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(836489827/2000000000 : ℝ)|^4911 ≤ (33242946746439/100000000000000 : ℝ)^3887
        have hw : |(836489827/2000000000 : ℝ)|=(836489827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4527949721/10000000000 : ℝ)|^4911 ≤ (9187377233243/25000000000000 : ℝ)^3887
        have hw : |(4527949721/10000000000 : ℝ)|=(4527949721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(771372081/2000000000 : ℝ)|^4911 ≤ (30007544309487/100000000000000 : ℝ)^3887
        have hw : |(771372081/2000000000 : ℝ)|=(771372081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1648_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (533/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1017/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16277/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2131/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16277/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2131/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16277/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2131/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16277/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2131/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16277/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2131/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16277/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2131/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2131/20000 : ℝ) ^ (4907/1024 : ℝ) ≤ (2187982021195559/100000000000000000000 : ℝ) := by
    have hpowers : (2131/20000 : ℝ)^4907 ≤ (2187982021195559/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2131 : ℕ)^4907*100000000000000000000^1024 ≤ 2187982021195559^1024*20000^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2131 20000 2187982021195559 100000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2131/20000 : ℝ)) (X := (2187982021195559/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16277/100000 : ℝ) ^ (4907/1024 : ℝ) ≤ (260429714837073/1562500000000000000 : ℝ) := by
    have hpowers : (16277/100000 : ℝ)^4907 ≤ (260429714837073/1562500000000000000 : ℝ)^1024 := by
      have hnat : (16277 : ℕ)^4907*1562500000000000000^1024 ≤ 260429714837073^1024*100000^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16277 100000 260429714837073 1562500000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16277/100000 : ℝ)) (X := (260429714837073/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002187982021195559/50000000000000000000 : ℝ) ≤ (10000091316682251/10000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (50002187982021195559/50000000000000000000 : ℝ)^1024 ≤ (10000091316682251/10000000000000000 : ℝ)^4907 := by
      have hnat : (50002187982021195559 : ℕ)^1024*10000000000000000^4907 ≤ 10000091316682251^4907*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002187982021195559 50000000000000000000 10000091316682251 10000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000091316682251/10000000000000000 : ℝ)) (X := (50002187982021195559/50000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018855483770768231/100000000000000000000 : ℝ) ≤ (5000196724832877/5000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (100018855483770768231/100000000000000000000 : ℝ)^1024 ≤ (5000196724832877/5000000000000000 : ℝ)^4907 := by
      have hnat : (100018855483770768231 : ℕ)^1024*5000000000000000^4907 ≤ 5000196724832877^4907*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018855483770768231 100000000000000000000 5000196724832877 5000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000196724832877/5000000000000000 : ℝ)) (X := (100018855483770768231/100000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781510429714837073/781250000000000000 : ℝ) ≤ (10000695582649257/10000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (781510429714837073/781250000000000000 : ℝ)^1024 ≤ (10000695582649257/10000000000000000 : ℝ)^4907 := by
      have hnat : (781510429714837073 : ℕ)^1024*10000000000000000^4907 ≤ 10000695582649257^4907*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781510429714837073 781250000000000000 10000695582649257 10000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000695582649257/10000000000000000 : ℝ)) (X := (781510429714837073/781250000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2187982021195559/100000000000000000000 : ℝ) ≤ ((1171126561010607629/1171250000000000000 : ℝ)+2*(100710994501/187400000000000 : ℝ)*(2131/20000 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (1171126561010607629/1171250000000000000 : ℝ)+2*(100710994501/187400000000000 : ℝ)*(2131/20000 : ℝ)=(10000091316682251/10000000000000000 : ℝ) by norm_num, show 1+2*(2187982021195559/100000000000000000000 : ℝ)=(50002187982021195559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(260429714837073/1562500000000000000 : ℝ)+(2187982021195559/100000000000000000000 : ℝ) ≤ ((1171126561010607629/1171250000000000000 : ℝ)+(100710994501/187400000000000 : ℝ)*((16277/100000 : ℝ)+(2131/20000 : ℝ)))^(4907/1024 : ℝ) := by
    rw [show (1171126561010607629/1171250000000000000 : ℝ)+(100710994501/187400000000000 : ℝ)*((16277/100000 : ℝ)+(2131/20000 : ℝ))=(5000196724832877/5000000000000000 : ℝ) by norm_num, show 1+(260429714837073/1562500000000000000 : ℝ)+(2187982021195559/100000000000000000000 : ℝ)=(100018855483770768231/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(260429714837073/1562500000000000000 : ℝ) ≤ ((1171126561010607629/1171250000000000000 : ℝ)+2*(100710994501/187400000000000 : ℝ)*(16277/100000 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (1171126561010607629/1171250000000000000 : ℝ)+2*(100710994501/187400000000000 : ℝ)*(16277/100000 : ℝ)=(10000695582649257/10000000000000000 : ℝ) by norm_num, show 1+2*(260429714837073/1562500000000000000 : ℝ)=(781510429714837073/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1171126561010607629/1171250000000000000 : ℝ)*(X 1 0+X 2 0)+(100710994501/187400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (2131/20000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (1171126561010607629/1171250000000000000 : ℝ)) (alpha := (100710994501/187400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1171126561010607629/1171250000000000000 : ℝ)*(X 0 1+X 2 1)+(100710994501/187400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (2131/20000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (1171126561010607629/1171250000000000000 : ℝ)) (alpha := (100710994501/187400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1171126561010607629/1171250000000000000 : ℝ)*(X 0 2+X 1 2)+(100710994501/187400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (2131/20000 : ℝ)) (hi := (16277/100000 : ℝ)) (c := (1171126561010607629/1171250000000000000 : ℝ)) (alpha := (100710994501/187400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-403280671/2500000000 : ℝ)*X 0 0+(2723981923/5000000000 : ℝ)*X 0 1+(647989521/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267400039/500000000 : ℝ)*X 1 0+(-1749058047/10000000000 : ℝ)*X 1 1+(5183916019/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213920029/400000000 : ℝ)*X 2 0+(1295978969/2500000000 : ℝ)*X 2 1+(-218632289/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((261392677/625000000 : ℝ)*X 0 0+(3851659037/10000000000 : ℝ)*X 0 1+(4533097061/10000000000 : ℝ)*X 0 2+(261392677/625000000 : ℝ)*X 1 0+(3851659037/10000000000 : ℝ)*X 1 1+(4533097061/10000000000 : ℝ)*X 1 2+(261392677/625000000 : ℝ)*X 2 0+(3851659037/10000000000 : ℝ)*X 2 1+(4533097061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1613187181/10000000000 : ℝ)*X 0 0+(1037182071/2000000000 : ℝ)*X 0 1+(2722974293/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2638738003/5000000000 : ℝ)*X 1 0+(-23234779/156250000 : ℝ)*X 1 1+(2722974293/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638738003/5000000000 : ℝ)*X 2 0+(2722974293/5000000000 : ℝ)*X 2 1+(-23234779/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((836489827/2000000000 : ℝ)*X 0 0+(4527949721/10000000000 : ℝ)*X 0 1+(771372081/2000000000 : ℝ)*X 0 2+(836489827/2000000000 : ℝ)*X 1 0+(4527949721/10000000000 : ℝ)*X 1 1+(771372081/2000000000 : ℝ)*X 1 2+(836489827/2000000000 : ℝ)*X 2 0+(4527949721/10000000000 : ℝ)*X 2 1+(771372081/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147413749713917461158070053/29281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1009253663/100000000000000 : ℝ)*(base19) + (212134019/20000000000000 : ℝ)*(base23) + (72278353/50000000000000 : ℝ)*(upper3) + (4899417/10000000000000 : ℝ)*(lower4) + (1313679772044619/50000000000000 : ℝ)*(major0) + (1313679772044619/50000000000000 : ℝ)*(major1) + (1313679772044619/50000000000000 : ℝ)*(major2) + (1893604997905841/50000000000000 : ℝ)*(sp0) + (946804966519981/25000000000000 : ℝ)*(sp1) + (1893609860046891/50000000000000 : ℝ)*(sp2) + (22929546920089/1562500000000 : ℝ)*(sp3) + (5439760953/50000000000000 : ℝ)*(sp4) + (9456971/10000000000000 : ℝ)*(sp6) + (3521072797/50000000000000 : ℝ)*(sp7) + (1467498045031289/100000000000000 : ℝ)*(f.failure) + (946805218833397/25000000000000 : ℝ)*(f.sum) + (42725129301661/4685000000000000000000000000 : ℝ)*base66 + (171968261324207899/58562500000000000000000000000000 : ℝ)*base68 + (278906015194832899/58562500000000000000000000000000 : ℝ)*base70 + (760742363367832899/58562500000000000000000000000000 : ℝ)*base72 + (17606571186511/4685000000000000000000000000 : ℝ)*base74 + (200246324119667101/58562500000000000000000000000000 : ℝ)*base75 + (147536152875957899/58562500000000000000000000000000 : ℝ)*base78 + (36723453792667101/58562500000000000000000000000000 : ℝ)*base79 + (35205968976051/4685000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5227513/1250000000000000000000 : ℝ)*base90 + (5227513/1250000000000000000000 : ℝ)*base92 + (5227513/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6916191941051847596112153/732031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1393275017/100000000000000 : ℝ)*(base19) + (150683629/10000000000000 : ℝ)*(base23) + (8732769/2000000000000 : ℝ)*(lower1) + (98933077/50000000000000 : ℝ)*(upper3) + (25590033/50000000000000 : ℝ)*(lower4) + (48904327/25000000000000 : ℝ)*(upper5) + (133391974832713/5000000000000 : ℝ)*(major0) + (133391974832713/5000000000000 : ℝ)*(major1) + (133391974832713/5000000000000 : ℝ)*(major2) + (620464919/50000000000000 : ℝ)*(sp2) + (384557076581317/10000000000000 : ℝ)*(sp4) + (480696171567269/12500000000000 : ℝ)*(sp5) + (1922784009023521/50000000000000 : ℝ)*(sp6) + (745053956281899/50000000000000 : ℝ)*(sp7) + (745053956281899/50000000000000 : ℝ)*(f.failure) + (384557076581317/10000000000000 : ℝ)*(f.sum) + (2705570678547/468500000000000000000000000 : ℝ)*base66 + (52381776211673727/5856250000000000000000000000000 : ℝ)*base67 + (17625710885663773/5856250000000000000000000000000 : ℝ)*base70 + (21234916776813773/5856250000000000000000000000000 : ℝ)*base72 + (1232357715519/234250000000000000000000000 : ℝ)*base74 + (110235133376438773/5856250000000000000000000000000 : ℝ)*base76 + (20841528395126273/5856250000000000000000000000000 : ℝ)*base78 + (69271951806763773/5856250000000000000000000000000 : ℝ)*base80 + (1690322251923/234250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5068117/625000000000000000000 : ℝ)*base89 + (5068117/625000000000000000000 : ℝ)*base91 + (5068117/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1648_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16277/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2131/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (533/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1017/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1648_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1648_box_0 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-677210397/5000000000 : ℝ)*x 0 + (5408558181/10000000000 : ℝ)*x 1 + (5408557101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677210397/5000000000 : ℝ)^4911 ≤ (7998726305537/100000000000000 : ℝ)^3887 := by
    have hnat : (677210397 : ℕ)^4911*100000000000000^3887 ≤ 7998726305537^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677210397 5000000000 7998726305537 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408558181/10000000000 : ℝ)^4911 ≤ (11500160661353/25000000000000 : ℝ)^3887 := by
    have hnat : (5408558181 : ℕ)^4911*25000000000000^3887 ≤ 11500160661353^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408558181 10000000000 11500160661353 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408557101/10000000000 : ℝ)^4911 ≤ (23000315519987/50000000000000 : ℝ)^3887 := by
    have hnat : (5408557101 : ℕ)^4911*50000000000000^3887 ≤ 23000315519987^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408557101 10000000000 23000315519987 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-677210397/5000000000 : ℝ), (5408558181/10000000000 : ℝ), (5408557101/10000000000 : ℝ)] ![(7998726305537/100000000000000 : ℝ), (11500160661353/25000000000000 : ℝ), (23000315519987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-677210397/5000000000 : ℝ)|^4911 ≤ (7998726305537/100000000000000 : ℝ)^3887
        have hw : |(-677210397/5000000000 : ℝ)|=(677210397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408558181/10000000000 : ℝ)|^4911 ≤ (11500160661353/25000000000000 : ℝ)^3887
        have hw : |(5408558181/10000000000 : ℝ)|=(5408558181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408557101/10000000000 : ℝ)|^4911 ≤ (23000315519987/50000000000000 : ℝ)^3887
        have hw : |(5408557101/10000000000 : ℝ)|=(5408557101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_1 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625554881/5000000000 : ℝ)*x 0 + (-787856993/5000000000 : ℝ)*x 1 + (1352139329/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625554881/5000000000 : ℝ)^4911 ≤ (44315271818589/100000000000000 : ℝ)^3887 := by
    have hnat : (2625554881 : ℕ)^4911*100000000000000^3887 ≤ 44315271818589^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625554881 5000000000 44315271818589 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (787856993/5000000000 : ℝ)^4911 ≤ (9684094818449/100000000000000 : ℝ)^3887 := by
    have hnat : (787856993 : ℕ)^4911*100000000000000^3887 ≤ 9684094818449^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787856993 5000000000 9684094818449 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352139329/2500000000 : ℝ)^4911 ≤ (11500158337579/25000000000000 : ℝ)^3887 := by
    have hnat : (1352139329 : ℕ)^4911*25000000000000^3887 ≤ 11500158337579^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352139329 2500000000 11500158337579 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625554881/5000000000 : ℝ), (-787856993/5000000000 : ℝ), (1352139329/2500000000 : ℝ)] ![(44315271818589/100000000000000 : ℝ), (9684094818449/100000000000000 : ℝ), (11500158337579/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625554881/5000000000 : ℝ)|^4911 ≤ (44315271818589/100000000000000 : ℝ)^3887
        have hw : |(2625554881/5000000000 : ℝ)|=(2625554881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-787856993/5000000000 : ℝ)|^4911 ≤ (9684094818449/100000000000000 : ℝ)^3887
        have hw : |(-787856993/5000000000 : ℝ)|=(787856993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352139329/2500000000 : ℝ)|^4911 ≤ (11500158337579/25000000000000 : ℝ)^3887
        have hw : |(1352139329/2500000000 : ℝ)|=(1352139329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_2 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251109177/10000000000 : ℝ)*x 0 + (1352139447/2500000000 : ℝ)*x 1 + (-1575714137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251109177/10000000000 : ℝ)^4911 ≤ (8863053116209/20000000000000 : ℝ)^3887 := by
    have hnat : (5251109177 : ℕ)^4911*20000000000000^3887 ≤ 8863053116209^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251109177 10000000000 8863053116209 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352139447/2500000000 : ℝ)^4911 ≤ (23000319211161/50000000000000 : ℝ)^3887 := by
    have hnat : (1352139447 : ℕ)^4911*50000000000000^3887 ≤ 23000319211161^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352139447 2500000000 23000319211161 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1575714137/10000000000 : ℝ)^4911 ≤ (1210511998869/12500000000000 : ℝ)^3887 := by
    have hnat : (1575714137 : ℕ)^4911*12500000000000^3887 ≤ 1210511998869^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1575714137 10000000000 1210511998869 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251109177/10000000000 : ℝ), (1352139447/2500000000 : ℝ), (-1575714137/10000000000 : ℝ)] ![(8863053116209/20000000000000 : ℝ), (23000319211161/50000000000000 : ℝ), (1210511998869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251109177/10000000000 : ℝ)|^4911 ≤ (8863053116209/20000000000000 : ℝ)^3887
        have hw : |(5251109177/10000000000 : ℝ)|=(5251109177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352139447/2500000000 : ℝ)|^4911 ≤ (23000319211161/50000000000000 : ℝ)^3887
        have hw : |(1352139447/2500000000 : ℝ)|=(1352139447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1575714137/10000000000 : ℝ)|^4911 ≤ (1210511998869/12500000000000 : ℝ)^3887
        have hw : |(-1575714137/10000000000 : ℝ)|=(1575714137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_3 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (891844083/2000000000 : ℝ)*x 0 + (506983681/1250000000 : ℝ)*x 1 + (4055868649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891844083/2000000000 : ℝ)^4911 ≤ (3604615350603/10000000000000 : ℝ)^3887 := by
    have hnat : (891844083 : ℕ)^4911*10000000000000^3887 ≤ 3604615350603^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891844083 2000000000 3604615350603 10000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506983681/1250000000 : ℝ)^4911 ≤ (6395385443447/20000000000000 : ℝ)^3887 := by
    have hnat : (506983681 : ℕ)^4911*20000000000000^3887 ≤ 6395385443447^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506983681 1250000000 6395385443447 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4055868649/10000000000 : ℝ)^4911 ≤ (31976919258301/100000000000000 : ℝ)^3887 := by
    have hnat : (4055868649 : ℕ)^4911*100000000000000^3887 ≤ 31976919258301^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4055868649 10000000000 31976919258301 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(891844083/2000000000 : ℝ), (506983681/1250000000 : ℝ), (4055868649/10000000000 : ℝ)] ![(3604615350603/10000000000000 : ℝ), (6395385443447/20000000000000 : ℝ), (31976919258301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(891844083/2000000000 : ℝ)|^4911 ≤ (3604615350603/10000000000000 : ℝ)^3887
        have hw : |(891844083/2000000000 : ℝ)|=(891844083/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506983681/1250000000 : ℝ)|^4911 ≤ (6395385443447/20000000000000 : ℝ)^3887
        have hw : |(506983681/1250000000 : ℝ)|=(506983681/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4055868649/10000000000 : ℝ)|^4911 ≤ (31976919258301/100000000000000 : ℝ)^3887
        have hw : |(4055868649/10000000000 : ℝ)|=(4055868649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_4 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1882434759/10000000000 : ℝ)*x 0 + (5215688621/10000000000 : ℝ)*x 1 + (5215689489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1882434759/10000000000 : ℝ)^4911 ≤ (12124128359573/100000000000000 : ℝ)^3887 := by
    have hnat : (1882434759 : ℕ)^4911*100000000000000^3887 ≤ 12124128359573^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882434759 10000000000 12124128359573 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215688621/10000000000 : ℝ)^4911 ≤ (21968965594649/50000000000000 : ℝ)^3887 := by
    have hnat : (5215688621 : ℕ)^4911*50000000000000^3887 ≤ 21968965594649^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215688621 10000000000 21968965594649 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215689489/10000000000 : ℝ)^4911 ≤ (5492242553479/12500000000000 : ℝ)^3887 := by
    have hnat : (5215689489 : ℕ)^4911*12500000000000^3887 ≤ 5492242553479^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215689489 10000000000 5492242553479 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1882434759/10000000000 : ℝ), (5215688621/10000000000 : ℝ), (5215689489/10000000000 : ℝ)] ![(12124128359573/100000000000000 : ℝ), (21968965594649/50000000000000 : ℝ), (5492242553479/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1882434759/10000000000 : ℝ)|^4911 ≤ (12124128359573/100000000000000 : ℝ)^3887
        have hw : |(-1882434759/10000000000 : ℝ)|=(1882434759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215688621/10000000000 : ℝ)|^4911 ≤ (21968965594649/50000000000000 : ℝ)^3887
        have hw : |(5215688621/10000000000 : ℝ)|=(5215688621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215689489/10000000000 : ℝ)|^4911 ≤ (5492242553479/12500000000000 : ℝ)^3887
        have hw : |(5215689489/10000000000 : ℝ)|=(5215689489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_5 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5383525589/10000000000 : ℝ)*x 0 + (-165836469/1000000000 : ℝ)*x 1 + (1303922327/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5383525589/10000000000 : ℝ)^4911 ≤ (45731812196007/100000000000000 : ℝ)^3887 := by
    have hnat : (5383525589 : ℕ)^4911*100000000000000^3887 ≤ 45731812196007^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383525589 10000000000 45731812196007 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165836469/1000000000 : ℝ)^4911 ≤ (5165124643311/50000000000000 : ℝ)^3887 := by
    have hnat : (165836469 : ℕ)^4911*50000000000000^3887 ≤ 5165124643311^3887*1000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165836469 1000000000 5165124643311 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303922327/2500000000 : ℝ)^4911 ≤ (10984484625341/25000000000000 : ℝ)^3887 := by
    have hnat : (1303922327 : ℕ)^4911*25000000000000^3887 ≤ 10984484625341^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303922327 2500000000 10984484625341 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5383525589/10000000000 : ℝ), (-165836469/1000000000 : ℝ), (1303922327/2500000000 : ℝ)] ![(45731812196007/100000000000000 : ℝ), (5165124643311/50000000000000 : ℝ), (10984484625341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5383525589/10000000000 : ℝ)|^4911 ≤ (45731812196007/100000000000000 : ℝ)^3887
        have hw : |(5383525589/10000000000 : ℝ)|=(5383525589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-165836469/1000000000 : ℝ)|^4911 ≤ (5165124643311/50000000000000 : ℝ)^3887
        have hw : |(-165836469/1000000000 : ℝ)|=(165836469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303922327/2500000000 : ℝ)|^4911 ≤ (10984484625341/25000000000000 : ℝ)^3887
        have hw : |(1303922327/2500000000 : ℝ)|=(1303922327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_6 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672940749/1250000000 : ℝ)*x 0 + (2607844277/5000000000 : ℝ)*x 1 + (-1658365161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672940749/1250000000 : ℝ)^4911 ≤ (22865908260633/50000000000000 : ℝ)^3887 := by
    have hnat : (672940749 : ℕ)^4911*50000000000000^3887 ≤ 22865908260633^3887*1250000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672940749 1250000000 22865908260633 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607844277/5000000000 : ℝ)^4911 ≤ (8787586095237/20000000000000 : ℝ)^3887 := by
    have hnat : (2607844277 : ℕ)^4911*20000000000000^3887 ≤ 8787586095237^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607844277 5000000000 8787586095237 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1658365161/10000000000 : ℝ)^4911 ≤ (1033025299349/10000000000000 : ℝ)^3887 := by
    have hnat : (1658365161 : ℕ)^4911*10000000000000^3887 ≤ 1033025299349^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658365161 10000000000 1033025299349 10000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672940749/1250000000 : ℝ), (2607844277/5000000000 : ℝ), (-1658365161/10000000000 : ℝ)] ![(22865908260633/50000000000000 : ℝ), (8787586095237/20000000000000 : ℝ), (1033025299349/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672940749/1250000000 : ℝ)|^4911 ≤ (22865908260633/50000000000000 : ℝ)^3887
        have hw : |(672940749/1250000000 : ℝ)|=(672940749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607844277/5000000000 : ℝ)|^4911 ≤ (8787586095237/20000000000000 : ℝ)^3887
        have hw : |(2607844277/5000000000 : ℝ)|=(2607844277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1658365161/10000000000 : ℝ)|^4911 ≤ (1033025299349/10000000000000 : ℝ)^3887
        have hw : |(-1658365161/10000000000 : ℝ)|=(1658365161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_7 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (779773223/2000000000 : ℝ)*x 0 + (4335720493/10000000000 : ℝ)*x 1 + (1083930087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (779773223/2000000000 : ℝ)^4911 ≤ (3042104971781/10000000000000 : ℝ)^3887 := by
    have hnat : (779773223 : ℕ)^4911*10000000000000^3887 ≤ 3042104971781^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779773223 2000000000 3042104971781 10000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4335720493/10000000000 : ℝ)^4911 ≤ (34789475869081/100000000000000 : ℝ)^3887 := by
    have hnat : (4335720493 : ℕ)^4911*100000000000000^3887 ≤ 34789475869081^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335720493 10000000000 34789475869081 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083930087/2500000000 : ℝ)^4911 ≤ (17394737199553/50000000000000 : ℝ)^3887 := by
    have hnat : (1083930087 : ℕ)^4911*50000000000000^3887 ≤ 17394737199553^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083930087 2500000000 17394737199553 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(779773223/2000000000 : ℝ), (4335720493/10000000000 : ℝ), (1083930087/2500000000 : ℝ)] ![(3042104971781/10000000000000 : ℝ), (34789475869081/100000000000000 : ℝ), (17394737199553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(779773223/2000000000 : ℝ)|^4911 ≤ (3042104971781/10000000000000 : ℝ)^3887
        have hw : |(779773223/2000000000 : ℝ)|=(779773223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4335720493/10000000000 : ℝ)|^4911 ≤ (34789475869081/100000000000000 : ℝ)^3887
        have hw : |(4335720493/10000000000 : ℝ)|=(4335720493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083930087/2500000000 : ℝ)|^4911 ≤ (17394737199553/50000000000000 : ℝ)^3887
        have hw : |(1083930087/2500000000 : ℝ)|=(1083930087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_8 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-884909911/5000000000 : ℝ)*x 0 + (5077025839/10000000000 : ℝ)*x 1 + (5438038139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (884909911/5000000000 : ℝ)^4911 ≤ (5607532537973/50000000000000 : ℝ)^3887 := by
    have hnat : (884909911 : ℕ)^4911*50000000000000^3887 ≤ 5607532537973^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      884909911 5000000000 5607532537973 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077025839/10000000000 : ℝ)^4911 ≤ (42467280104499/100000000000000 : ℝ)^3887 := by
    have hnat : (5077025839 : ℕ)^4911*100000000000000^3887 ≤ 42467280104499^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077025839 10000000000 42467280104499 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438038139/10000000000 : ℝ)^4911 ≤ (46317654808599/100000000000000 : ℝ)^3887 := by
    have hnat : (5438038139 : ℕ)^4911*100000000000000^3887 ≤ 46317654808599^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438038139 10000000000 46317654808599 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-884909911/5000000000 : ℝ), (5077025839/10000000000 : ℝ), (5438038139/10000000000 : ℝ)] ![(5607532537973/50000000000000 : ℝ), (42467280104499/100000000000000 : ℝ), (46317654808599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-884909911/5000000000 : ℝ)|^4911 ≤ (5607532537973/50000000000000 : ℝ)^3887
        have hw : |(-884909911/5000000000 : ℝ)|=(884909911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077025839/10000000000 : ℝ)|^4911 ≤ (42467280104499/100000000000000 : ℝ)^3887
        have hw : |(5077025839/10000000000 : ℝ)|=(5077025839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438038139/10000000000 : ℝ)|^4911 ≤ (46317654808599/100000000000000 : ℝ)^3887
        have hw : |(5438038139/10000000000 : ℝ)|=(5438038139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_9 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307717201/2500000000 : ℝ)*x 0 + (-1562650859/10000000000 : ℝ)*x 1 + (5438039121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307717201/2500000000 : ℝ)^4911 ≤ (11024890736663/25000000000000 : ℝ)^3887 := by
    have hnat : (1307717201 : ℕ)^4911*25000000000000^3887 ≤ 11024890736663^3887*2500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307717201 2500000000 11024890736663 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562650859/10000000000 : ℝ)^4911 ≤ (9582771663431/100000000000000 : ℝ)^3887 := by
    have hnat : (1562650859 : ℕ)^4911*100000000000000^3887 ≤ 9582771663431^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562650859 10000000000 9582771663431 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438039121/10000000000 : ℝ)^4911 ≤ (23158832688037/50000000000000 : ℝ)^3887 := by
    have hnat : (5438039121 : ℕ)^4911*50000000000000^3887 ≤ 23158832688037^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438039121 10000000000 23158832688037 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307717201/2500000000 : ℝ), (-1562650859/10000000000 : ℝ), (5438039121/10000000000 : ℝ)] ![(11024890736663/25000000000000 : ℝ), (9582771663431/100000000000000 : ℝ), (23158832688037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307717201/2500000000 : ℝ)|^4911 ≤ (11024890736663/25000000000000 : ℝ)^3887
        have hw : |(1307717201/2500000000 : ℝ)|=(1307717201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1562650859/10000000000 : ℝ)|^4911 ≤ (9582771663431/100000000000000 : ℝ)^3887
        have hw : |(-1562650859/10000000000 : ℝ)|=(1562650859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438039121/10000000000 : ℝ)|^4911 ≤ (23158832688037/50000000000000 : ℝ)^3887
        have hw : |(5438039121/10000000000 : ℝ)|=(5438039121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_10 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615434451/5000000000 : ℝ)*x 0 + (1087607937/2000000000 : ℝ)*x 1 + (-1562649941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615434451/5000000000 : ℝ)^4911 ≤ (44099563990511/100000000000000 : ℝ)^3887 := by
    have hnat : (2615434451 : ℕ)^4911*100000000000000^3887 ≤ 44099563990511^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615434451 5000000000 44099563990511 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087607937/2000000000 : ℝ)^4911 ≤ (46317671445377/100000000000000 : ℝ)^3887 := by
    have hnat : (1087607937 : ℕ)^4911*100000000000000^3887 ≤ 46317671445377^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087607937 2000000000 46317671445377 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1562649941/10000000000 : ℝ)^4911 ≤ (191655291017/2000000000000 : ℝ)^3887 := by
    have hnat : (1562649941 : ℕ)^4911*2000000000000^3887 ≤ 191655291017^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562649941 10000000000 191655291017 2000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615434451/5000000000 : ℝ), (1087607937/2000000000 : ℝ), (-1562649941/10000000000 : ℝ)] ![(44099563990511/100000000000000 : ℝ), (46317671445377/100000000000000 : ℝ), (191655291017/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615434451/5000000000 : ℝ)|^4911 ≤ (44099563990511/100000000000000 : ℝ)^3887
        have hw : |(2615434451/5000000000 : ℝ)|=(2615434451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087607937/2000000000 : ℝ)|^4911 ≤ (46317671445377/100000000000000 : ℝ)^3887
        have hw : |(1087607937/2000000000 : ℝ)|=(1087607937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1562649941/10000000000 : ℝ)|^4911 ≤ (191655291017/2000000000000 : ℝ)^3887
        have hw : |(-1562649941/10000000000 : ℝ)|=(1562649941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_11 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4542493149/10000000000 : ℝ)*x 0 + (4013016483/10000000000 : ℝ)*x 1 + (2006507079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4542493149/10000000000 : ℝ)^4911 ≤ (9224676104457/25000000000000 : ℝ)^3887 := by
    have hnat : (4542493149 : ℕ)^4911*25000000000000^3887 ≤ 9224676104457^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542493149 10000000000 9224676104457 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013016483/10000000000 : ℝ)^4911 ≤ (3155065933089/10000000000000 : ℝ)^3887 := by
    have hnat : (4013016483 : ℕ)^4911*10000000000000^3887 ≤ 3155065933089^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013016483 10000000000 3155065933089 10000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2006507079/5000000000 : ℝ)^4911 ≤ (6310127247201/20000000000000 : ℝ)^3887 := by
    have hnat : (2006507079 : ℕ)^4911*20000000000000^3887 ≤ 6310127247201^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006507079 5000000000 6310127247201 20000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4542493149/10000000000 : ℝ), (4013016483/10000000000 : ℝ), (2006507079/5000000000 : ℝ)] ![(9224676104457/25000000000000 : ℝ), (3155065933089/10000000000000 : ℝ), (6310127247201/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4542493149/10000000000 : ℝ)|^4911 ≤ (9224676104457/25000000000000 : ℝ)^3887
        have hw : |(4542493149/10000000000 : ℝ)|=(4542493149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013016483/10000000000 : ℝ)|^4911 ≤ (3155065933089/10000000000000 : ℝ)^3887
        have hw : |(4013016483/10000000000 : ℝ)|=(4013016483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2006507079/5000000000 : ℝ)|^4911 ≤ (6310127247201/20000000000000 : ℝ)^3887
        have hw : |(2006507079/5000000000 : ℝ)|=(2006507079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_12 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73264761/500000000 : ℝ)*x 0 + (1108381317/2000000000 : ℝ)*x 1 + (103917297/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73264761/500000000 : ℝ)^4911 ≤ (8834756389877/100000000000000 : ℝ)^3887 := by
    have hnat : (73264761 : ℕ)^4911*100000000000000^3887 ≤ 8834756389877^3887*500000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73264761 500000000 8834756389877 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1108381317/2000000000 : ℝ)^4911 ≤ (47438200445449/100000000000000 : ℝ)^3887 := by
    have hnat : (1108381317 : ℕ)^4911*100000000000000^3887 ≤ 47438200445449^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1108381317 2000000000 47438200445449 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103917297/200000000 : ℝ)^4911 ≤ (5465880394971/12500000000000 : ℝ)^3887 := by
    have hnat : (103917297 : ℕ)^4911*12500000000000^3887 ≤ 5465880394971^3887*200000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103917297 200000000 5465880394971 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73264761/500000000 : ℝ), (1108381317/2000000000 : ℝ), (103917297/200000000 : ℝ)] ![(8834756389877/100000000000000 : ℝ), (47438200445449/100000000000000 : ℝ), (5465880394971/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73264761/500000000 : ℝ)|^4911 ≤ (8834756389877/100000000000000 : ℝ)^3887
        have hw : |(-73264761/500000000 : ℝ)|=(73264761/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1108381317/2000000000 : ℝ)|^4911 ≤ (47438200445449/100000000000000 : ℝ)^3887
        have hw : |(1108381317/2000000000 : ℝ)|=(1108381317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(103917297/200000000 : ℝ)|^4911 ≤ (5465880394971/12500000000000 : ℝ)^3887
        have hw : |(103917297/200000000 : ℝ)|=(103917297/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_13 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2698573069/5000000000 : ℝ)*x 0 + (-333314993/2000000000 : ℝ)*x 1 + (519586517/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2698573069/5000000000 : ℝ)^4911 ≤ (2293902274371/5000000000000 : ℝ)^3887 := by
    have hnat : (2698573069 : ℕ)^4911*5000000000000^3887 ≤ 2293902274371^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698573069 5000000000 2293902274371 5000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (333314993/2000000000 : ℝ)^4911 ≤ (10394907937293/100000000000000 : ℝ)^3887 := by
    have hnat : (333314993 : ℕ)^4911*100000000000000^3887 ≤ 10394907937293^3887*2000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      333314993 2000000000 10394907937293 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519586517/1000000000 : ℝ)^4911 ≤ (5465880820283/12500000000000 : ℝ)^3887 := by
    have hnat : (519586517 : ℕ)^4911*12500000000000^3887 ≤ 5465880820283^3887*1000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519586517 1000000000 5465880820283 12500000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2698573069/5000000000 : ℝ), (-333314993/2000000000 : ℝ), (519586517/1000000000 : ℝ)] ![(2293902274371/5000000000000 : ℝ), (10394907937293/100000000000000 : ℝ), (5465880820283/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2698573069/5000000000 : ℝ)|^4911 ≤ (2293902274371/5000000000000 : ℝ)^3887
        have hw : |(2698573069/5000000000 : ℝ)|=(2698573069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-333314993/2000000000 : ℝ)|^4911 ≤ (10394907937293/100000000000000 : ℝ)^3887
        have hw : |(-333314993/2000000000 : ℝ)|=(333314993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519586517/1000000000 : ℝ)|^4911 ≤ (5465880820283/12500000000000 : ℝ)^3887
        have hw : |(519586517/1000000000 : ℝ)|=(519586517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_14 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397145381/10000000000 : ℝ)*x 0 + (5195865593/10000000000 : ℝ)*x 1 + (-1666575427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397145381/10000000000 : ℝ)^4911 ≤ (45878037357393/100000000000000 : ℝ)^3887 := by
    have hnat : (5397145381 : ℕ)^4911*100000000000000^3887 ≤ 45878037357393^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397145381 10000000000 45878037357393 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195865593/10000000000 : ℝ)^4911 ≤ (43727051059939/100000000000000 : ℝ)^3887 := by
    have hnat : (5195865593 : ℕ)^4911*100000000000000^3887 ≤ 43727051059939^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195865593 10000000000 43727051059939 100000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1666575427/10000000000 : ℝ)^4911 ≤ (5197455789031/50000000000000 : ℝ)^3887 := by
    have hnat : (1666575427 : ℕ)^4911*50000000000000^3887 ≤ 5197455789031^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1666575427 10000000000 5197455789031 50000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397145381/10000000000 : ℝ), (5195865593/10000000000 : ℝ), (-1666575427/10000000000 : ℝ)] ![(45878037357393/100000000000000 : ℝ), (43727051059939/100000000000000 : ℝ), (5197455789031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397145381/10000000000 : ℝ)|^4911 ≤ (45878037357393/100000000000000 : ℝ)^3887
        have hw : |(5397145381/10000000000 : ℝ)|=(5397145381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195865593/10000000000 : ℝ)|^4911 ≤ (43727051059939/100000000000000 : ℝ)^3887
        have hw : |(5195865593/10000000000 : ℝ)|=(5195865593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1666575427/10000000000 : ℝ)|^4911 ≤ (5197455789031/50000000000000 : ℝ)^3887
        have hw : |(-1666575427/10000000000 : ℝ)|=(1666575427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1648_box_15 (p : ℝ) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3839642149/10000000000 : ℝ)*x 0 + (2182215937/5000000000 : ℝ)*x 1 + (4364433253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3839642149/10000000000 : ℝ)^4911 ≤ (7459597277727/25000000000000 : ℝ)^3887 := by
    have hnat : (3839642149 : ℕ)^4911*25000000000000^3887 ≤ 7459597277727^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3839642149 10000000000 7459597277727 25000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2182215937/5000000000 : ℝ)^4911 ≤ (1403231937371/4000000000000 : ℝ)^3887 := by
    have hnat : (2182215937 : ℕ)^4911*4000000000000^3887 ≤ 1403231937371^3887*5000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182215937 5000000000 1403231937371 4000000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4364433253/10000000000 : ℝ)^4911 ≤ (2192550777411/6250000000000 : ℝ)^3887 := by
    have hnat : (4364433253 : ℕ)^4911*6250000000000^3887 ≤ 2192550777411^3887*10000000000^4911 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364433253 10000000000 2192550777411 6250000000000 4911 3887 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4911/1024 : ℝ)) 4911 3887 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3839642149/10000000000 : ℝ), (2182215937/5000000000 : ℝ), (4364433253/10000000000 : ℝ)] ![(7459597277727/25000000000000 : ℝ), (1403231937371/4000000000000 : ℝ), (2192550777411/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3839642149/10000000000 : ℝ)|^4911 ≤ (7459597277727/25000000000000 : ℝ)^3887
        have hw : |(3839642149/10000000000 : ℝ)|=(3839642149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2182215937/5000000000 : ℝ)|^4911 ≤ (1403231937371/4000000000000 : ℝ)^3887
        have hw : |(2182215937/5000000000 : ℝ)|=(2182215937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4364433253/10000000000 : ℝ)|^4911 ≤ (2192550777411/6250000000000 : ℝ)^3887
        have hw : |(4364433253/10000000000 : ℝ)|=(4364433253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1648_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1017/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (533/5000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65059/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(14651/25000 : ℝ) ∧ (2029/2500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (22051/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1017/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (533/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1017/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (533/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1017/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (533/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1017/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (533/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1017/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (533/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1017/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (533/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (533/5000 : ℝ) ^ (4907/1024 : ℝ) ≤ (274113316080363/12500000000000000000 : ℝ) := by
    have hpowers : (533/5000 : ℝ)^4907 ≤ (274113316080363/12500000000000000000 : ℝ)^1024 := by
      have hnat : (533 : ℕ)^4907*12500000000000000000^1024 ≤ 274113316080363^1024*5000^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        533 5000 274113316080363 12500000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (533/5000 : ℝ)) (X := (274113316080363/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1017/6250 : ℝ) ^ (4907/1024 : ℝ) ≤ (16642981250214697/100000000000000000000 : ℝ) := by
    have hpowers : (1017/6250 : ℝ)^4907 ≤ (16642981250214697/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1017 : ℕ)^4907*100000000000000000000^1024 ≤ 16642981250214697^1024*6250^4907 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1017 6250 16642981250214697 100000000000000000000 4907 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1017/6250 : ℝ)) (X := (16642981250214697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250274113316080363/6250000000000000000 : ℝ) ≤ (5000045761102911/5000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (6250274113316080363/6250000000000000000 : ℝ)^1024 ≤ (5000045761102911/5000000000000000 : ℝ)^4907 := by
      have hnat : (6250274113316080363 : ℕ)^1024*5000000000000000^4907 ≤ 5000045761102911^4907*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250274113316080363 6250000000000000000 5000045761102911 5000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000045761102911/5000000000000000 : ℝ)) (X := (6250274113316080363/6250000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018835887778857601/100000000000000000000 : ℝ) ≤ (10000393040794677/10000000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (100018835887778857601/100000000000000000000 : ℝ)^1024 ≤ (10000393040794677/10000000000000000 : ℝ)^4907 := by
      have hnat : (100018835887778857601 : ℕ)^1024*10000000000000000^4907 ≤ 10000393040794677^4907*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018835887778857601 100000000000000000000 10000393040794677 10000000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000393040794677/10000000000000000 : ℝ)) (X := (100018835887778857601/100000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016642981250214697/50000000000000000000 : ℝ) ≤ (2500173639845883/2500000000000000 : ℝ) ^ (4907/1024 : ℝ) := by
    have hpowers : (50016642981250214697/50000000000000000000 : ℝ)^1024 ≤ (2500173639845883/2500000000000000 : ℝ)^4907 := by
      have hnat : (50016642981250214697 : ℕ)^1024*2500000000000000^4907 ≤ 2500173639845883^4907*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016642981250214697 50000000000000000000 2500173639845883 2500000000000000 1024 4907 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500173639845883/2500000000000000 : ℝ)) (X := (50016642981250214697/50000000000000000000 : ℝ)) (by norm_num) 4907 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(274113316080363/12500000000000000000 : ℝ) ≤ ((3507130327894042779/3507500000000000000 : ℝ)+2*(60303717771/112240000000000 : ℝ)*(533/5000 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (3507130327894042779/3507500000000000000 : ℝ)+2*(60303717771/112240000000000 : ℝ)*(533/5000 : ℝ)=(5000045761102911/5000000000000000 : ℝ) by norm_num, show 1+2*(274113316080363/12500000000000000000 : ℝ)=(6250274113316080363/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16642981250214697/100000000000000000000 : ℝ)+(274113316080363/12500000000000000000 : ℝ) ≤ ((3507130327894042779/3507500000000000000 : ℝ)+(60303717771/112240000000000 : ℝ)*((1017/6250 : ℝ)+(533/5000 : ℝ)))^(4907/1024 : ℝ) := by
    rw [show (3507130327894042779/3507500000000000000 : ℝ)+(60303717771/112240000000000 : ℝ)*((1017/6250 : ℝ)+(533/5000 : ℝ))=(10000393040794677/10000000000000000 : ℝ) by norm_num, show 1+(16642981250214697/100000000000000000000 : ℝ)+(274113316080363/12500000000000000000 : ℝ)=(100018835887778857601/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16642981250214697/100000000000000000000 : ℝ) ≤ ((3507130327894042779/3507500000000000000 : ℝ)+2*(60303717771/112240000000000 : ℝ)*(1017/6250 : ℝ))^(4907/1024 : ℝ) := by
    rw [show (3507130327894042779/3507500000000000000 : ℝ)+2*(60303717771/112240000000000 : ℝ)*(1017/6250 : ℝ)=(2500173639845883/2500000000000000 : ℝ) by norm_num, show 1+2*(16642981250214697/100000000000000000000 : ℝ)=(50016642981250214697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3507130327894042779/3507500000000000000 : ℝ)*(X 1 0+X 2 0)+(60303717771/112240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (533/5000 : ℝ)) (hi := (1017/6250 : ℝ)) (c := (3507130327894042779/3507500000000000000 : ℝ)) (alpha := (60303717771/112240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3507130327894042779/3507500000000000000 : ℝ)*(X 0 1+X 2 1)+(60303717771/112240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (533/5000 : ℝ)) (hi := (1017/6250 : ℝ)) (c := (3507130327894042779/3507500000000000000 : ℝ)) (alpha := (60303717771/112240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3507130327894042779/3507500000000000000 : ℝ)*(X 0 2+X 1 2)+(60303717771/112240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4907/1024 : ℝ)) (lo := (533/5000 : ℝ)) (hi := (1017/6250 : ℝ)) (c := (3507130327894042779/3507500000000000000 : ℝ)) (alpha := (60303717771/112240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-677210397/5000000000 : ℝ)*X 0 0+(5408558181/10000000000 : ℝ)*X 0 1+(5408557101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2625554881/5000000000 : ℝ)*X 1 0+(-787856993/5000000000 : ℝ)*X 1 1+(1352139329/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5251109177/10000000000 : ℝ)*X 2 0+(1352139447/2500000000 : ℝ)*X 2 1+(-1575714137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((891844083/2000000000 : ℝ)*X 0 0+(506983681/1250000000 : ℝ)*X 0 1+(4055868649/10000000000 : ℝ)*X 0 2+(891844083/2000000000 : ℝ)*X 1 0+(506983681/1250000000 : ℝ)*X 1 1+(4055868649/10000000000 : ℝ)*X 1 2+(891844083/2000000000 : ℝ)*X 2 0+(506983681/1250000000 : ℝ)*X 2 1+(4055868649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1882434759/10000000000 : ℝ)*X 0 0+(5215688621/10000000000 : ℝ)*X 0 1+(5215689489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5383525589/10000000000 : ℝ)*X 1 0+(-165836469/1000000000 : ℝ)*X 1 1+(1303922327/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((672940749/1250000000 : ℝ)*X 2 0+(2607844277/5000000000 : ℝ)*X 2 1+(-1658365161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((779773223/2000000000 : ℝ)*X 0 0+(4335720493/10000000000 : ℝ)*X 0 1+(1083930087/2500000000 : ℝ)*X 0 2+(779773223/2000000000 : ℝ)*X 1 0+(4335720493/10000000000 : ℝ)*X 1 1+(1083930087/2500000000 : ℝ)*X 1 2+(779773223/2000000000 : ℝ)*X 2 0+(4335720493/10000000000 : ℝ)*X 2 1+(1083930087/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-884909911/5000000000 : ℝ)*X 0 0+(5077025839/10000000000 : ℝ)*X 0 1+(5438038139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1307717201/2500000000 : ℝ)*X 1 0+(-1562650859/10000000000 : ℝ)*X 1 1+(5438039121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2615434451/5000000000 : ℝ)*X 2 0+(1087607937/2000000000 : ℝ)*X 2 1+(-1562649941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4542493149/10000000000 : ℝ)*X 0 0+(4013016483/10000000000 : ℝ)*X 0 1+(2006507079/5000000000 : ℝ)*X 0 2+(4542493149/10000000000 : ℝ)*X 1 0+(4013016483/10000000000 : ℝ)*X 1 1+(2006507079/5000000000 : ℝ)*X 1 2+(4542493149/10000000000 : ℝ)*X 2 0+(4013016483/10000000000 : ℝ)*X 2 1+(2006507079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-73264761/500000000 : ℝ)*X 0 0+(1108381317/2000000000 : ℝ)*X 0 1+(103917297/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2698573069/5000000000 : ℝ)*X 1 0+(-333314993/2000000000 : ℝ)*X 1 1+(519586517/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5397145381/10000000000 : ℝ)*X 2 0+(5195865593/10000000000 : ℝ)*X 2 1+(-1666575427/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3839642149/10000000000 : ℝ)*X 0 0+(2182215937/5000000000 : ℝ)*X 0 1+(4364433253/10000000000 : ℝ)*X 0 2+(3839642149/10000000000 : ℝ)*X 1 0+(2182215937/5000000000 : ℝ)*X 1 1+(4364433253/10000000000 : ℝ)*X 1 2+(3839642149/10000000000 : ℝ)*X 2 0+(2182215937/5000000000 : ℝ)*X 2 1+(4364433253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1648_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65059/100000 : ℝ) ≤ (-445676923738810501806494261007/685058593750000000000000000000 : ℝ) := by norm_num
    linear_combination (12679141/100000000000000 : ℝ)*(lower0) + (26353437/100000000000000 : ℝ)*(upper1) + (49954153/100000000000000 : ℝ)*(lower4) + (877568746239071/50000000000000 : ℝ)*(major0) + (877568746239071/50000000000000 : ℝ)*(major1) + (877568746239071/50000000000000 : ℝ)*(major2) + (99185339/25000000000000 : ℝ)*(sp1) + (5967468447/50000000000000 : ℝ)*(sp2) + (2180057733/100000000000000 : ℝ)*(sp3) + (1275815742815259/50000000000000 : ℝ)*(sp4) + (637909308105677/25000000000000 : ℝ)*(sp5) + (255162569422717/10000000000000 : ℝ)*(sp6) + (980320762330281/100000000000000 : ℝ)*(sp7) + (3071766773/50000000000000 : ℝ)*(sp12) + (490161471194007/50000000000000 : ℝ)*(f.failure) + (79738675911377/3125000000000 : ℝ)*(f.sum) + (7840687341027/2806000000000000000000000000 : ℝ)*base66 + (259994442831000441/175375000000000000000000000000000 : ℝ)*base68 + (277928401355749559/175375000000000000000000000000000 : ℝ)*base69 + (361503911076875441/175375000000000000000000000000000 : ℝ)*base72 + (1003234827531/561200000000000000000000000 : ℝ)*base73 + (1279065432478500441/175375000000000000000000000000000 : ℝ)*base76 + (113082872499625441/175375000000000000000000000000000 : ℝ)*base78 + (310556206492500441/175375000000000000000000000000000 : ℝ)*base80 + (16154734662801/2806000000000000000000000000 : ℝ)*base82 + (1259081/625000000000000000000 : ℝ)*base89 + (1259081/625000000000000000000 : ℝ)*base91 + (1259081/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (14651/25000 : ℝ) ≤ (102781394187914088102354262652913/175375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8364827/25000000000000 : ℝ)*(lower1) + (4520653/50000000000000 : ℝ)*(upper2) + (15759341/100000000000000 : ℝ)*(upper3) + (3604441/1562500000000 : ℝ)*(lower5) + (1845262405145101/100000000000000 : ℝ)*(major0) + (1845262405145101/100000000000000 : ℝ)*(major1) + (922631202572551/50000000000000 : ℝ)*(major2) + (2640324958462749/100000000000000 : ℝ)*(sp0) + (264032751888571/10000000000000 : ℝ)*(sp1) + (2640316537058793/100000000000000 : ℝ)*(sp2) + (515327153296799/50000000000000 : ℝ)*(sp3) + (10981826917/100000000000000 : ℝ)*(sp6) + (1859569891/25000000000000 : ℝ)*(sp7) + (32005287/1250000000000 : ℝ)*(sp8) + (515330872436581/50000000000000 : ℝ)*(f.failure) + (264032751888571/10000000000000 : ℝ)*(f.sum) + (1127676656183/11224000000000000000000000000 : ℝ)*base66 + (1078549961761338179/350750000000000000000000000000000 : ℝ)*base67 + (455200626381442151/43843750000000000000000000000000 : ℝ)*base69 + (44241505052411821/350750000000000000000000000000000 : ℝ)*base72 + (15243675648809/11224000000000000000000000000 : ℝ)*base73 + (218919981499785901/43843750000000000000000000000000 : ℝ)*base75 + (1688431849736505571/350750000000000000000000000000000 : ℝ)*base78 + (860693348138755571/350750000000000000000000000000000 : ℝ)*base80 + (20741187432881/5612000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (4524277/625000000000000000000 : ℝ)*base90 + (4524277/625000000000000000000 : ℝ)*base92 + (10774277/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (2029/2500 : ℝ) ≤ (17792345760119305028520108819213/21921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10343351/10000000000000 : ℝ)*(upper3) + (81466367/25000000000000 : ℝ)*(upper4) + (43540631/50000000000000 : ℝ)*(lower5) + (970216247453327/50000000000000 : ℝ)*(major0) + (970216247453327/50000000000000 : ℝ)*(major1) + (970216247453327/50000000000000 : ℝ)*(major2) + (1140836831/100000000000000 : ℝ)*(sp0) + (58321748107/100000000000000 : ℝ)*(sp1) + (20591041793/10000000000000 : ℝ)*(sp2) + (43915584519/100000000000000 : ℝ)*(sp3) + (34624889642859/1250000000000 : ℝ)*(sp8) + (692483497629361/25000000000000 : ℝ)*(sp9) + (138489320092381/5000000000000 : ℝ)*(sp10) + (135471823658781/12500000000000 : ℝ)*(sp11) + (67738656553423/6250000000000 : ℝ)*(f.failure) + (2769992312265551/100000000000000 : ℝ)*(f.sum) + (10278153453619/2806000000000000000000000000 : ℝ)*base65 + (560022395689906983/175375000000000000000000000000000 : ℝ)*base67 + (732149233400281983/175375000000000000000000000000000 : ℝ)*base69 + (421584811082593017/175375000000000000000000000000000 : ℝ)*base72 + (7750986473329/2806000000000000000000000000 : ℝ)*base73 + (791498145828406983/175375000000000000000000000000000 : ℝ)*base75 + (1030709709664906983/175375000000000000000000000000000 : ℝ)*base77 + (1429658257846531983/175375000000000000000000000000000 : ℝ)*base79 + (8532780761007/2806000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (525109/78125000000000000000 : ℝ)*base89 + (525109/78125000000000000000 : ℝ)*base91 + (525109/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-22051/25000 : ℝ) ≤ (-19335427698441032832977966509857/21921875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2222677/3125000000000 : ℝ)*(lower0) + (20228351/20000000000000 : ℝ)*(lower1) + (118239719/50000000000000 : ℝ)*(lower4) + (124025493180293/6250000000000 : ℝ)*(major0) + (124025493180293/6250000000000 : ℝ)*(major1) + (124025493180293/6250000000000 : ℝ)*(major2) + (2787182343/50000000000000 : ℝ)*(sp0) + (12835809993/20000000000000 : ℝ)*(sp5) + (7719456137/10000000000000 : ℝ)*(sp6) + (34336757517/100000000000000 : ℝ)*(sp7) + (1444914990507957/50000000000000 : ℝ)*(sp12) + (722442844082659/25000000000000 : ℝ)*(sp13) + (288975836081923/10000000000000 : ℝ)*(sp14) + (554173198708479/50000000000000 : ℝ)*(sp15) + (44335229366979/4000000000000 : ℝ)*(f.failure) + (14449177776903/500000000000 : ℝ)*(f.sum) + (2331741620887/1403000000000000000000000000 : ℝ)*base66 + (45523497836181811/10960937500000000000000000000000 : ℝ)*base67 + (94135493076410497/21921875000000000000000000000000 : ℝ)*base69 + (145387711302058253/21921875000000000000000000000000 : ℝ)*base72 + (3155441676663/1403000000000000000000000000 : ℝ)*base73 + (24589130450441747/21921875000000000000000000000000 : ℝ)*base75 + (3568614256573157/5480468750000000000000000000000 : ℝ)*base78 + (5854683433485617/1370117187500000000000000000000 : ℝ)*base79 + (568601214041/701500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (10243/50000000000000000000 : ℝ)*base90 + (10243/50000000000000000000 : ℝ)*base92 + (10243/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1648_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1017/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (533/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65059/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14651/25000 : ℝ) else (2029/2500 : ℝ) ≤ X j i ∧ X j i ≤ (22051/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1648_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1648_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65059/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14651/25000 : ℝ) else (2029/2500 : ℝ) ≤ X j i ∧ X j i ≤ (22051/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1648_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1648_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1648_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4907/1024 : ℝ) ≤ p) (hpb : p ≤ (4911/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (22379583/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (511/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2647/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65059/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(14651/25000 : ℝ) else (2029/2500 : ℝ) ≤ X j i ∧ X j i ≤ (22051/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1648_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
