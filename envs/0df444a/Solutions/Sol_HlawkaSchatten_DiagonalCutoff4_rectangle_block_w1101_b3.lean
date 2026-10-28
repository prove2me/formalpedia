-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1101_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:01:29.641072+00:00
-- url     : https://prove2.me/submissions/b1a8a571-8776-4766-bc43-ffc0a41c9fd0

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
theorem support_rectangle_w1101_s9_0 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2186654251/10000000000 : ℝ)*x 0 + (5393712347/10000000000 : ℝ)*x 1 + (1053020767/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186654251/10000000000 : ℝ)^4147 ≤ (6641569560811/50000000000000 : ℝ)^3123 := by
    have hnat : (2186654251 : ℕ)^4147*50000000000000^3123 ≤ 6641569560811^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186654251 10000000000 6641569560811 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393712347/10000000000 : ℝ)^4147 ≤ (22026551587447/50000000000000 : ℝ)^3123 := by
    have hnat : (5393712347 : ℕ)^4147*50000000000000^3123 ≤ 22026551587447^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393712347 10000000000 22026551587447 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053020767/2000000000 : ℝ)^4147 ≤ (42663757693059/100000000000000 : ℝ)^3123 := by
    have hnat : (1053020767 : ℕ)^4147*100000000000000^3123 ≤ 42663757693059^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053020767 2000000000 42663757693059 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2186654251/10000000000 : ℝ), (5393712347/10000000000 : ℝ), (1053020767/2000000000 : ℝ)] ![(6641569560811/50000000000000 : ℝ), (22026551587447/50000000000000 : ℝ), (42663757693059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2186654251/10000000000 : ℝ)|^4147 ≤ (6641569560811/50000000000000 : ℝ)^3123
        have hw : |(-2186654251/10000000000 : ℝ)|=(2186654251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393712347/10000000000 : ℝ)|^4147 ≤ (22026551587447/50000000000000 : ℝ)^3123
        have hw : |(5393712347/10000000000 : ℝ)|=(5393712347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053020767/2000000000 : ℝ)|^4147 ≤ (42663757693059/100000000000000 : ℝ)^3123
        have hw : |(1053020767/2000000000 : ℝ)|=(1053020767/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s9_1 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336219859/2500000000 : ℝ)*x 0 + (-450379309/2000000000 : ℝ)*x 1 + (5265103819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336219859/2500000000 : ℝ)^4147 ≤ (43524272094211/100000000000000 : ℝ)^3123 := by
    have hnat : (1336219859 : ℕ)^4147*100000000000000^3123 ≤ 43524272094211^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336219859 2500000000 43524272094211 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450379309/2000000000 : ℝ)^4147 ≤ (6905985188837/50000000000000 : ℝ)^3123 := by
    have hnat : (450379309 : ℕ)^4147*50000000000000^3123 ≤ 6905985188837^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450379309 2000000000 6905985188837 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265103819/10000000000 : ℝ)^4147 ≤ (21331878760449/50000000000000 : ℝ)^3123 := by
    have hnat : (5265103819 : ℕ)^4147*50000000000000^3123 ≤ 21331878760449^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265103819 10000000000 21331878760449 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336219859/2500000000 : ℝ), (-450379309/2000000000 : ℝ), (5265103819/10000000000 : ℝ)] ![(43524272094211/100000000000000 : ℝ), (6905985188837/50000000000000 : ℝ), (21331878760449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336219859/2500000000 : ℝ)|^4147 ≤ (43524272094211/100000000000000 : ℝ)^3123
        have hw : |(1336219859/2500000000 : ℝ)|=(1336219859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450379309/2000000000 : ℝ)|^4147 ≤ (6905985188837/50000000000000 : ℝ)^3123
        have hw : |(-450379309/2000000000 : ℝ)|=(450379309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265103819/10000000000 : ℝ)|^4147 ≤ (21331878760449/50000000000000 : ℝ)^3123
        have hw : |(5265103819/10000000000 : ℝ)|=(5265103819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s9_2 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534487943/1000000000 : ℝ)*x 0 + (5265103831/10000000000 : ℝ)*x 1 + (-281487067/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534487943/1000000000 : ℝ)^4147 ≤ (43524272029331/100000000000000 : ℝ)^3123 := by
    have hnat : (534487943 : ℕ)^4147*100000000000000^3123 ≤ 43524272029331^3123*1000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534487943 1000000000 43524272029331 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265103831/10000000000 : ℝ)^4147 ≤ (21331878825009/50000000000000 : ℝ)^3123 := by
    have hnat : (5265103831 : ℕ)^4147*50000000000000^3123 ≤ 21331878825009^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265103831 10000000000 21331878825009 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281487067/1250000000 : ℝ)^4147 ≤ (13811970304373/100000000000000 : ℝ)^3123 := by
    have hnat : (281487067 : ℕ)^4147*100000000000000^3123 ≤ 13811970304373^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281487067 1250000000 13811970304373 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534487943/1000000000 : ℝ), (5265103831/10000000000 : ℝ), (-281487067/1250000000 : ℝ)] ![(43524272029331/100000000000000 : ℝ), (21331878825009/50000000000000 : ℝ), (13811970304373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534487943/1000000000 : ℝ)|^4147 ≤ (43524272029331/100000000000000 : ℝ)^3123
        have hw : |(534487943/1000000000 : ℝ)|=(534487943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265103831/10000000000 : ℝ)|^4147 ≤ (21331878825009/50000000000000 : ℝ)^3123
        have hw : |(5265103831/10000000000 : ℝ)|=(5265103831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-281487067/1250000000 : ℝ)|^4147 ≤ (13811970304373/100000000000000 : ℝ)^3123
        have hw : |(-281487067/1250000000 : ℝ)|=(281487067/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s9_3 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4370483953/10000000000 : ℝ)*x 0 + (849086291/2000000000 : ℝ)*x 1 + (1124809699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370483953/10000000000 : ℝ)^4147 ≤ (33316763936009/100000000000000 : ℝ)^3123 := by
    have hnat : (4370483953 : ℕ)^4147*100000000000000^3123 ≤ 33316763936009^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370483953 10000000000 33316763936009 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849086291/2000000000 : ℝ)^4147 ≤ (32056874668051/100000000000000 : ℝ)^3123 := by
    have hnat : (849086291 : ℕ)^4147*100000000000000^3123 ≤ 32056874668051^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849086291 2000000000 32056874668051 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1124809699/2500000000 : ℝ)^4147 ≤ (1082073792839/3125000000000 : ℝ)^3123 := by
    have hnat : (1124809699 : ℕ)^4147*3125000000000^3123 ≤ 1082073792839^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124809699 2500000000 1082073792839 3125000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370483953/10000000000 : ℝ), (849086291/2000000000 : ℝ), (1124809699/2500000000 : ℝ)] ![(33316763936009/100000000000000 : ℝ), (32056874668051/100000000000000 : ℝ), (1082073792839/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370483953/10000000000 : ℝ)|^4147 ≤ (33316763936009/100000000000000 : ℝ)^3123
        have hw : |(4370483953/10000000000 : ℝ)|=(4370483953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849086291/2000000000 : ℝ)|^4147 ≤ (32056874668051/100000000000000 : ℝ)^3123
        have hw : |(849086291/2000000000 : ℝ)|=(849086291/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1124809699/2500000000 : ℝ)|^4147 ≤ (1082073792839/3125000000000 : ℝ)^3123
        have hw : |(1124809699/2500000000 : ℝ)|=(1124809699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s9_4 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1093329917/5000000000 : ℝ)*x 0 + (1053085101/2000000000 : ℝ)*x 1 + (2696694527/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093329917/5000000000 : ℝ)^4147 ≤ (3320796039163/25000000000000 : ℝ)^3123 := by
    have hnat : (1093329917 : ℕ)^4147*25000000000000^3123 ≤ 3320796039163^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093329917 5000000000 3320796039163 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053085101/2000000000 : ℝ)^4147 ≤ (21333609456207/50000000000000 : ℝ)^3123 := by
    have hnat : (1053085101 : ℕ)^4147*50000000000000^3123 ≤ 21333609456207^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053085101 2000000000 21333609456207 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696694527/5000000000 : ℝ)^4147 ≤ (44049596925451/100000000000000 : ℝ)^3123 := by
    have hnat : (2696694527 : ℕ)^4147*100000000000000^3123 ≤ 44049596925451^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696694527 5000000000 44049596925451 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1093329917/5000000000 : ℝ), (1053085101/2000000000 : ℝ), (2696694527/5000000000 : ℝ)] ![(3320796039163/25000000000000 : ℝ), (21333609456207/50000000000000 : ℝ), (44049596925451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1093329917/5000000000 : ℝ)|^4147 ≤ (3320796039163/25000000000000 : ℝ)^3123
        have hw : |(-1093329917/5000000000 : ℝ)|=(1093329917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053085101/2000000000 : ℝ)|^4147 ≤ (21333609456207/50000000000000 : ℝ)^3123
        have hw : |(1053085101/2000000000 : ℝ)|=(1053085101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696694527/5000000000 : ℝ)|^4147 ≤ (44049596925451/100000000000000 : ℝ)^3123
        have hw : |(2696694527/5000000000 : ℝ)|=(2696694527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_s9_5 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8740987/20000000 : ℝ)*x 0 + (4498602959/10000000000 : ℝ)*x 1 + (849213969/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8740987/20000000 : ℝ)^4147 ≤ (33316860577231/100000000000000 : ℝ)^3123 := by
    have hnat : (8740987 : ℕ)^4147*100000000000000^3123 ≤ 33316860577231^3123*20000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8740987 20000000 33316860577231 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498602959/10000000000 : ℝ)^4147 ≤ (34619863581943/100000000000000 : ℝ)^3123 := by
    have hnat : (4498602959 : ℕ)^4147*100000000000000^3123 ≤ 34619863581943^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498602959 10000000000 34619863581943 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849213969/2000000000 : ℝ)^4147 ≤ (32063275820619/100000000000000 : ℝ)^3123 := by
    have hnat : (849213969 : ℕ)^4147*100000000000000^3123 ≤ 32063275820619^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849213969 2000000000 32063275820619 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8740987/20000000 : ℝ), (4498602959/10000000000 : ℝ), (849213969/2000000000 : ℝ)] ![(33316860577231/100000000000000 : ℝ), (34619863581943/100000000000000 : ℝ), (32063275820619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8740987/20000000 : ℝ)|^4147 ≤ (33316860577231/100000000000000 : ℝ)^3123
        have hw : |(8740987/20000000 : ℝ)|=(8740987/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498602959/10000000000 : ℝ)|^4147 ≤ (34619863581943/100000000000000 : ℝ)^3123
        have hw : |(4498602959/10000000000 : ℝ)|=(4498602959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849213969/2000000000 : ℝ)|^4147 ≤ (32063275820619/100000000000000 : ℝ)^3123
        have hw : |(849213969/2000000000 : ℝ)|=(849213969/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1101_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (113/1000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1753/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11299/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11299/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11299/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11299/100000 : ℝ) ^ (8293/2048 : ℝ) ≤ (7318622984786237/50000000000000000000 : ℝ) := by
    have hpowers : (11299/100000 : ℝ)^8293 ≤ (7318622984786237/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11299 : ℕ)^8293*50000000000000000000^2048 ≤ 7318622984786237^2048*100000^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11299 100000 7318622984786237 50000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11299/100000 : ℝ)) (X := (7318622984786237/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1753/12500 : ℝ) ^ (8293/2048 : ℝ) ≤ (35108671848353113/100000000000000000000 : ℝ) := by
    have hpowers : (1753/12500 : ℝ)^8293 ≤ (35108671848353113/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1753 : ℕ)^8293*100000000000000000000^2048 ≤ 35108671848353113^2048*12500^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753 12500 35108671848353113 100000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1753/12500 : ℝ)) (X := (35108671848353113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007318622984786237/25000000000000000000 : ℝ) ≤ (10000722869313563/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (25007318622984786237/25000000000000000000 : ℝ)^2048 ≤ (10000722869313563/10000000000000000 : ℝ)^8293 := by
      have hnat : (25007318622984786237 : ℕ)^2048*10000000000000000^8293 ≤ 10000722869313563^8293*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007318622984786237 25000000000000000000 10000722869313563 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000722869313563/10000000000000000 : ℝ)) (X := (25007318622984786237/25000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049745917817925587/100000000000000000000 : ℝ) ≤ (1250153533948391/1250000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (100049745917817925587/100000000000000000000 : ℝ)^2048 ≤ (1250153533948391/1250000000000000 : ℝ)^8293 := by
      have hnat : (100049745917817925587 : ℕ)^2048*1250000000000000^8293 ≤ 1250153533948391^8293*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049745917817925587 100000000000000000000 1250153533948391 1250000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250153533948391/1250000000000000 : ℝ)) (X := (100049745917817925587/100000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035108671848353113/50000000000000000000 : ℝ) ≤ (10001733673860693/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (50035108671848353113/50000000000000000000 : ℝ)^2048 ≤ (10001733673860693/10000000000000000 : ℝ)^8293 := by
      have hnat : (50035108671848353113 : ℕ)^2048*10000000000000000^8293 ≤ 10001733673860693^8293*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035108671848353113 50000000000000000000 10001733673860693 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001733673860693/10000000000000000 : ℝ)) (X := (50035108671848353113/50000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7318622984786237/50000000000000000000 : ℝ) ≤ ((5448109747660287461/5450000000000000000 : ℝ)+2*(101080454713/54500000000000 : ℝ)*(11299/100000 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (5448109747660287461/5450000000000000000 : ℝ)+2*(101080454713/54500000000000 : ℝ)*(11299/100000 : ℝ)=(10000722869313563/10000000000000000 : ℝ) by norm_num, show 1+2*(7318622984786237/50000000000000000000 : ℝ)=(25007318622984786237/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35108671848353113/100000000000000000000 : ℝ)+(7318622984786237/50000000000000000000 : ℝ) ≤ ((5448109747660287461/5450000000000000000 : ℝ)+(101080454713/54500000000000 : ℝ)*((1753/12500 : ℝ)+(11299/100000 : ℝ)))^(8293/2048 : ℝ) := by
    rw [show (5448109747660287461/5450000000000000000 : ℝ)+(101080454713/54500000000000 : ℝ)*((1753/12500 : ℝ)+(11299/100000 : ℝ))=(1250153533948391/1250000000000000 : ℝ) by norm_num, show 1+(35108671848353113/100000000000000000000 : ℝ)+(7318622984786237/50000000000000000000 : ℝ)=(100049745917817925587/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35108671848353113/100000000000000000000 : ℝ) ≤ ((5448109747660287461/5450000000000000000 : ℝ)+2*(101080454713/54500000000000 : ℝ)*(1753/12500 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (5448109747660287461/5450000000000000000 : ℝ)+2*(101080454713/54500000000000 : ℝ)*(1753/12500 : ℝ)=(10001733673860693/10000000000000000 : ℝ) by norm_num, show 1+2*(35108671848353113/100000000000000000000 : ℝ)=(50035108671848353113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5448109747660287461/5450000000000000000 : ℝ)*(X 1 0+X 2 0)+(101080454713/54500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (5448109747660287461/5450000000000000000 : ℝ)) (alpha := (101080454713/54500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5448109747660287461/5450000000000000000 : ℝ)*(X 0 1+X 2 1)+(101080454713/54500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (5448109747660287461/5450000000000000000 : ℝ)) (alpha := (101080454713/54500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5448109747660287461/5450000000000000000 : ℝ)*(X 0 2+X 1 2)+(101080454713/54500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (11299/100000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (5448109747660287461/5450000000000000000 : ℝ)) (alpha := (101080454713/54500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2186654251/10000000000 : ℝ)*X 0 0+(5393712347/10000000000 : ℝ)*X 0 1+(1053020767/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336219859/2500000000 : ℝ)*X 1 0+(-450379309/2000000000 : ℝ)*X 1 1+(5265103819/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534487943/1000000000 : ℝ)*X 2 0+(5265103831/10000000000 : ℝ)*X 2 1+(-281487067/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370483953/10000000000 : ℝ)*X 0 0+(849086291/2000000000 : ℝ)*X 0 1+(1124809699/2500000000 : ℝ)*X 0 2+(4370483953/10000000000 : ℝ)*X 1 0+(849086291/2000000000 : ℝ)*X 1 1+(1124809699/2500000000 : ℝ)*X 1 2+(4370483953/10000000000 : ℝ)*X 2 0+(849086291/2000000000 : ℝ)*X 2 1+(1124809699/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1093329917/5000000000 : ℝ)*X 0 0+(1053085101/2000000000 : ℝ)*X 0 1+(2696694527/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((8740987/20000000 : ℝ)*X 0 0+(4498602959/10000000000 : ℝ)*X 0 1+(849213969/2000000000 : ℝ)*X 0 2+(8740987/20000000 : ℝ)*X 1 0+(4498602959/10000000000 : ℝ)*X 1 1+(849213969/2000000000 : ℝ)*X 1 2+(8740987/20000000 : ℝ)*X 2 0+(4498602959/10000000000 : ℝ)*X 2 1+(849213969/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (288535727416130161191596343/68125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (803699203/100000000000000 : ℝ)*(base19) + (73132243/10000000000000 : ℝ)*(base23) + (17009583/50000000000000 : ℝ)*(lower2) + (96980289/100000000000000 : ℝ)*(upper3) + (30813343/50000000000000 : ℝ)*(upper5) + (2928899251656121/50000000000000 : ℝ)*(major0) + (2928899251656121/50000000000000 : ℝ)*(major1) + (2928899251656121/50000000000000 : ℝ)*(major2) + (3887778472113537/50000000000000 : ℝ)*(sp0) + (3887788637421127/50000000000000 : ℝ)*(sp1) + (7775577347219027/100000000000000 : ℝ)*(sp2) + (788001406264887/20000000000000 : ℝ)*(sp3) + (21134314383/100000000000000 : ℝ)*(sp4) + (5877789513/50000000000000 : ℝ)*(sp5) + (3940018786903461/100000000000000 : ℝ)*(f.failure) + (7775578078541457/100000000000000 : ℝ)*(f.sum) + (5036335576729/2725000000000000000000000000 : ℝ)*base66 + (263693699912501219/272500000000000000000000000000000 : ℝ)*base68 + (3147774226787501219/272500000000000000000000000000000 : ℝ)*base70 + (164335853029998781/272500000000000000000000000000000 : ℝ)*base71 + (2068237972479/2725000000000000000000000000 : ℝ)*base74 + (2783380565252501219/272500000000000000000000000000000 : ℝ)*base76 + (263060195455001219/272500000000000000000000000000000 : ℝ)*base78 + (4054651391152501219/272500000000000000000000000000000 : ℝ)*base80 + (1412789017251/681250000000000000000000000 : ℝ)*base82 + (798541/500000000000000000000 : ℝ)*base90 + (798541/500000000000000000000 : ℝ)*base92 + (798541/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1101_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1101_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1101_box_0 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2058389551/10000000000 : ℝ)*x 0 + (336055391/625000000 : ℝ)*x 1 + (5376886337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058389551/10000000000 : ℝ)^4147 ≤ (1532322714361/12500000000000 : ℝ)^3123 := by
    have hnat : (2058389551 : ℕ)^4147*12500000000000^3123 ≤ 1532322714361^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058389551 10000000000 1532322714361 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336055391/625000000 : ℝ)^4147 ≤ (43870708698451/100000000000000 : ℝ)^3123 := by
    have hnat : (336055391 : ℕ)^4147*100000000000000^3123 ≤ 43870708698451^3123*625000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336055391 625000000 43870708698451 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376886337/10000000000 : ℝ)^4147 ≤ (1096767739401/2500000000000 : ℝ)^3123 := by
    have hnat : (5376886337 : ℕ)^4147*2500000000000^3123 ≤ 1096767739401^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376886337 10000000000 1096767739401 2500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2058389551/10000000000 : ℝ), (336055391/625000000 : ℝ), (5376886337/10000000000 : ℝ)] ![(1532322714361/12500000000000 : ℝ), (43870708698451/100000000000000 : ℝ), (1096767739401/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2058389551/10000000000 : ℝ)|^4147 ≤ (1532322714361/12500000000000 : ℝ)^3123
        have hw : |(-2058389551/10000000000 : ℝ)|=(2058389551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336055391/625000000 : ℝ)|^4147 ≤ (43870708698451/100000000000000 : ℝ)^3123
        have hw : |(336055391/625000000 : ℝ)|=(336055391/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376886337/10000000000 : ℝ)|^4147 ≤ (1096767739401/2500000000000 : ℝ)^3123
        have hw : |(5376886337/10000000000 : ℝ)|=(5376886337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_1 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661947871/1250000000 : ℝ)*x 0 + (-542136403/2500000000 : ℝ)*x 1 + (2688443151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661947871/1250000000 : ℝ)^4147 ≤ (21496012739913/50000000000000 : ℝ)^3123 := by
    have hnat : (661947871 : ℕ)^4147*50000000000000^3123 ≤ 21496012739913^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661947871 1250000000 21496012739913 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542136403/2500000000 : ℝ)^4147 ≤ (6568632656291/50000000000000 : ℝ)^3123 := by
    have hnat : (542136403 : ℕ)^4147*50000000000000^3123 ≤ 6568632656291^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542136403 2500000000 6568632656291 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688443151/5000000000 : ℝ)^4147 ≤ (8774141839367/20000000000000 : ℝ)^3123 := by
    have hnat : (2688443151 : ℕ)^4147*20000000000000^3123 ≤ 8774141839367^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688443151 5000000000 8774141839367 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661947871/1250000000 : ℝ), (-542136403/2500000000 : ℝ), (2688443151/5000000000 : ℝ)] ![(21496012739913/50000000000000 : ℝ), (6568632656291/50000000000000 : ℝ), (8774141839367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661947871/1250000000 : ℝ)|^4147 ≤ (21496012739913/50000000000000 : ℝ)^3123
        have hw : |(661947871/1250000000 : ℝ)|=(661947871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-542136403/2500000000 : ℝ)|^4147 ≤ (6568632656291/50000000000000 : ℝ)^3123
        have hw : |(-542136403/2500000000 : ℝ)|=(542136403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688443151/5000000000 : ℝ)|^4147 ≤ (8774141839367/20000000000000 : ℝ)^3123
        have hw : |(2688443151/5000000000 : ℝ)|=(2688443151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_2 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295582857/10000000000 : ℝ)*x 0 + (33605539/62500000 : ℝ)*x 1 + (-542136461/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295582857/10000000000 : ℝ)^4147 ≤ (21496012141599/50000000000000 : ℝ)^3123 := by
    have hnat : (5295582857 : ℕ)^4147*50000000000000^3123 ≤ 21496012141599^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295582857 10000000000 21496012141599 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33605539/62500000 : ℝ)^4147 ≤ (43870708525101/100000000000000 : ℝ)^3123 := by
    have hnat : (33605539 : ℕ)^4147*100000000000000^3123 ≤ 43870708525101^3123*62500000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33605539 62500000 43870708525101 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542136461/2500000000 : ℝ)^4147 ≤ (1642158397363/12500000000000 : ℝ)^3123 := by
    have hnat : (542136461 : ℕ)^4147*12500000000000^3123 ≤ 1642158397363^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542136461 2500000000 1642158397363 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295582857/10000000000 : ℝ), (33605539/62500000 : ℝ), (-542136461/2500000000 : ℝ)] ![(21496012141599/50000000000000 : ℝ), (43870708525101/100000000000000 : ℝ), (1642158397363/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295582857/10000000000 : ℝ)|^4147 ≤ (21496012141599/50000000000000 : ℝ)^3123
        have hw : |(5295582857/10000000000 : ℝ)|=(5295582857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33605539/62500000 : ℝ)|^4147 ≤ (43870708525101/100000000000000 : ℝ)^3123
        have hw : |(33605539/62500000 : ℝ)|=(33605539/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-542136461/2500000000 : ℝ)|^4147 ≤ (1642158397363/12500000000000 : ℝ)^3123
        have hw : |(-542136461/2500000000 : ℝ)|=(542136461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_3 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (895694549/2000000000 : ℝ)*x 0 + (2159312969/5000000000 : ℝ)*x 1 + (539828301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (895694549/2000000000 : ℝ)^4147 ≤ (34414303355177/100000000000000 : ℝ)^3123 := by
    have hnat : (895694549 : ℕ)^4147*100000000000000^3123 ≤ 34414303355177^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895694549 2000000000 34414303355177 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2159312969/5000000000 : ℝ)^4147 ≤ (32792845948823/100000000000000 : ℝ)^3123 := by
    have hnat : (2159312969 : ℕ)^4147*100000000000000^3123 ≤ 32792845948823^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159312969 5000000000 32792845948823 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539828301/1250000000 : ℝ)^4147 ≤ (32792850687897/100000000000000 : ℝ)^3123 := by
    have hnat : (539828301 : ℕ)^4147*100000000000000^3123 ≤ 32792850687897^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539828301 1250000000 32792850687897 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(895694549/2000000000 : ℝ), (2159312969/5000000000 : ℝ), (539828301/1250000000 : ℝ)] ![(34414303355177/100000000000000 : ℝ), (32792845948823/100000000000000 : ℝ), (32792850687897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(895694549/2000000000 : ℝ)|^4147 ≤ (34414303355177/100000000000000 : ℝ)^3123
        have hw : |(895694549/2000000000 : ℝ)|=(895694549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2159312969/5000000000 : ℝ)|^4147 ≤ (32792845948823/100000000000000 : ℝ)^3123
        have hw : |(2159312969/5000000000 : ℝ)|=(2159312969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539828301/1250000000 : ℝ)|^4147 ≤ (32792850687897/100000000000000 : ℝ)^3123
        have hw : |(539828301/1250000000 : ℝ)|=(539828301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_4 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1158148739/5000000000 : ℝ)*x 0 + (2640297961/5000000000 : ℝ)*x 1 + (1056119173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1158148739/5000000000 : ℝ)^4147 ≤ (1792366660967/12500000000000 : ℝ)^3123 := by
    have hnat : (1158148739 : ℕ)^4147*12500000000000^3123 ≤ 1792366660967^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158148739 5000000000 1792366660967 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640297961/5000000000 : ℝ)^4147 ≤ (42830533654973/100000000000000 : ℝ)^3123 := by
    have hnat : (2640297961 : ℕ)^4147*100000000000000^3123 ≤ 42830533654973^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640297961 5000000000 42830533654973 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056119173/2000000000 : ℝ)^4147 ≤ (42830533041059/100000000000000 : ℝ)^3123 := by
    have hnat : (1056119173 : ℕ)^4147*100000000000000^3123 ≤ 42830533041059^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056119173 2000000000 42830533041059 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1158148739/5000000000 : ℝ), (2640297961/5000000000 : ℝ), (1056119173/2000000000 : ℝ)] ![(1792366660967/12500000000000 : ℝ), (42830533654973/100000000000000 : ℝ), (42830533041059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1158148739/5000000000 : ℝ)|^4147 ≤ (1792366660967/12500000000000 : ℝ)^3123
        have hw : |(-1158148739/5000000000 : ℝ)|=(1158148739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640297961/5000000000 : ℝ)|^4147 ≤ (42830533654973/100000000000000 : ℝ)^3123
        have hw : |(2640297961/5000000000 : ℝ)|=(2640297961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056119173/2000000000 : ℝ)|^4147 ≤ (42830533041059/100000000000000 : ℝ)^3123
        have hw : |(1056119173/2000000000 : ℝ)|=(1056119173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_5 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363675059/10000000000 : ℝ)*x 0 + (-2206299143/10000000000 : ℝ)*x 1 + (5280595829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363675059/10000000000 : ℝ)^4147 ≤ (43727630670033/100000000000000 : ℝ)^3123 := by
    have hnat : (5363675059 : ℕ)^4147*100000000000000^3123 ≤ 43727630670033^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363675059 10000000000 43727630670033 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206299143/10000000000 : ℝ)^4147 ≤ (6720918333907/50000000000000 : ℝ)^3123 := by
    have hnat : (2206299143 : ℕ)^4147*50000000000000^3123 ≤ 6720918333907^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206299143 10000000000 6720918333907 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5280595829/10000000000 : ℝ)^4147 ≤ (10707633163331/25000000000000 : ℝ)^3123 := by
    have hnat : (5280595829 : ℕ)^4147*25000000000000^3123 ≤ 10707633163331^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280595829 10000000000 10707633163331 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363675059/10000000000 : ℝ), (-2206299143/10000000000 : ℝ), (5280595829/10000000000 : ℝ)] ![(43727630670033/100000000000000 : ℝ), (6720918333907/50000000000000 : ℝ), (10707633163331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363675059/10000000000 : ℝ)|^4147 ≤ (43727630670033/100000000000000 : ℝ)^3123
        have hw : |(5363675059/10000000000 : ℝ)|=(5363675059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2206299143/10000000000 : ℝ)|^4147 ≤ (6720918333907/50000000000000 : ℝ)^3123
        have hw : |(-2206299143/10000000000 : ℝ)|=(2206299143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5280595829/10000000000 : ℝ)|^4147 ≤ (10707633163331/25000000000000 : ℝ)^3123
        have hw : |(5280595829/10000000000 : ℝ)|=(5280595829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_6 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681837553/5000000000 : ℝ)*x 0 + (5280595927/10000000000 : ℝ)*x 1 + (-2206298949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681837553/5000000000 : ℝ)^4147 ≤ (43727631178841/100000000000000 : ℝ)^3123 := by
    have hnat : (2681837553 : ℕ)^4147*100000000000000^3123 ≤ 43727631178841^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681837553 5000000000 43727631178841 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280595927/10000000000 : ℝ)^4147 ≤ (1713221348353/4000000000000 : ℝ)^3123 := by
    have hnat : (5280595927 : ℕ)^4147*4000000000000^3123 ≤ 1713221348353^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280595927 10000000000 1713221348353 4000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206298949/10000000000 : ℝ)^4147 ≤ (6720917549163/50000000000000 : ℝ)^3123 := by
    have hnat : (2206298949 : ℕ)^4147*50000000000000^3123 ≤ 6720917549163^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206298949 10000000000 6720917549163 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681837553/5000000000 : ℝ), (5280595927/10000000000 : ℝ), (-2206298949/10000000000 : ℝ)] ![(43727631178841/100000000000000 : ℝ), (1713221348353/4000000000000 : ℝ), (6720917549163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681837553/5000000000 : ℝ)|^4147 ≤ (43727631178841/100000000000000 : ℝ)^3123
        have hw : |(2681837553/5000000000 : ℝ)|=(2681837553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280595927/10000000000 : ℝ)|^4147 ≤ (1713221348353/4000000000000 : ℝ)^3123
        have hw : |(5280595927/10000000000 : ℝ)|=(5280595927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2206298949/10000000000 : ℝ)|^4147 ≤ (6720917549163/50000000000000 : ℝ)^3123
        have hw : |(-2206298949/10000000000 : ℝ)|=(2206298949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_7 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (852430209/2000000000 : ℝ)*x 0 + (885353159/2000000000 : ℝ)*x 1 + (4426765919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (852430209/2000000000 : ℝ)^4147 ≤ (8056156607303/25000000000000 : ℝ)^3123 := by
    have hnat : (852430209 : ℕ)^4147*25000000000000^3123 ≤ 8056156607303^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852430209 2000000000 8056156607303 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885353159/2000000000 : ℝ)^4147 ≤ (33887686150101/100000000000000 : ℝ)^3123 := by
    have hnat : (885353159 : ℕ)^4147*100000000000000^3123 ≤ 33887686150101^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885353159 2000000000 33887686150101 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4426765919/10000000000 : ℝ)^4147 ≤ (33887687410591/100000000000000 : ℝ)^3123 := by
    have hnat : (4426765919 : ℕ)^4147*100000000000000^3123 ≤ 33887687410591^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4426765919 10000000000 33887687410591 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(852430209/2000000000 : ℝ), (885353159/2000000000 : ℝ), (4426765919/10000000000 : ℝ)] ![(8056156607303/25000000000000 : ℝ), (33887686150101/100000000000000 : ℝ), (33887687410591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(852430209/2000000000 : ℝ)|^4147 ≤ (8056156607303/25000000000000 : ℝ)^3123
        have hw : |(852430209/2000000000 : ℝ)|=(852430209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(885353159/2000000000 : ℝ)|^4147 ≤ (33887686150101/100000000000000 : ℝ)^3123
        have hw : |(885353159/2000000000 : ℝ)|=(885353159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4426765919/10000000000 : ℝ)|^4147 ≤ (33887687410591/100000000000000 : ℝ)^3123
        have hw : |(4426765919/10000000000 : ℝ)|=(4426765919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_8 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1131206817/5000000000 : ℝ)*x 0 + (1043037749/2000000000 : ℝ)*x 1 + (2693245509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1131206817/5000000000 : ℝ)^4147 ≤ (13897693278427/100000000000000 : ℝ)^3123 := by
    have hnat : (1131206817 : ℕ)^4147*100000000000000^3123 ≤ 13897693278427^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131206817 5000000000 13897693278427 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043037749/2000000000 : ℝ)^4147 ≤ (42127505475403/100000000000000 : ℝ)^3123 := by
    have hnat : (1043037749 : ℕ)^4147*100000000000000^3123 ≤ 42127505475403^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043037749 2000000000 42127505475403 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693245509/5000000000 : ℝ)^4147 ≤ (21987400615607/50000000000000 : ℝ)^3123 := by
    have hnat : (2693245509 : ℕ)^4147*50000000000000^3123 ≤ 21987400615607^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693245509 5000000000 21987400615607 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1131206817/5000000000 : ℝ), (1043037749/2000000000 : ℝ), (2693245509/5000000000 : ℝ)] ![(13897693278427/100000000000000 : ℝ), (42127505475403/100000000000000 : ℝ), (21987400615607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1131206817/5000000000 : ℝ)|^4147 ≤ (13897693278427/100000000000000 : ℝ)^3123
        have hw : |(-1131206817/5000000000 : ℝ)|=(1131206817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043037749/2000000000 : ℝ)|^4147 ≤ (42127505475403/100000000000000 : ℝ)^3123
        have hw : |(1043037749/2000000000 : ℝ)|=(1043037749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693245509/5000000000 : ℝ)|^4147 ≤ (21987400615607/50000000000000 : ℝ)^3123
        have hw : |(2693245509/5000000000 : ℝ)|=(2693245509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_9 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288787277/10000000000 : ℝ)*x 0 + (-2164710103/10000000000 : ℝ)*x 1 + (2693245453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288787277/10000000000 : ℝ)^4147 ≤ (10729695102447/25000000000000 : ℝ)^3123 := by
    have hnat : (5288787277 : ℕ)^4147*25000000000000^3123 ≤ 10729695102447^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288787277 10000000000 10729695102447 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164710103/10000000000 : ℝ)^4147 ≤ (1638302444151/12500000000000 : ℝ)^3123 := by
    have hnat : (2164710103 : ℕ)^4147*12500000000000^3123 ≤ 1638302444151^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164710103 10000000000 1638302444151 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693245453/5000000000 : ℝ)^4147 ≤ (5496850002131/12500000000000 : ℝ)^3123 := by
    have hnat : (2693245453 : ℕ)^4147*12500000000000^3123 ≤ 5496850002131^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693245453 5000000000 5496850002131 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288787277/10000000000 : ℝ), (-2164710103/10000000000 : ℝ), (2693245453/5000000000 : ℝ)] ![(10729695102447/25000000000000 : ℝ), (1638302444151/12500000000000 : ℝ), (5496850002131/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288787277/10000000000 : ℝ)|^4147 ≤ (10729695102447/25000000000000 : ℝ)^3123
        have hw : |(5288787277/10000000000 : ℝ)|=(5288787277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2164710103/10000000000 : ℝ)|^4147 ≤ (1638302444151/12500000000000 : ℝ)^3123
        have hw : |(-2164710103/10000000000 : ℝ)|=(2164710103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693245453/5000000000 : ℝ)|^4147 ≤ (5496850002131/12500000000000 : ℝ)^3123
        have hw : |(2693245453/5000000000 : ℝ)|=(2693245453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_10 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288787393/10000000000 : ℝ)*x 0 + (336655687/625000000 : ℝ)*x 1 + (-270588729/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288787393/10000000000 : ℝ)^4147 ≤ (2682423853737/6250000000000 : ℝ)^3123 := by
    have hnat : (5288787393 : ℕ)^4147*6250000000000^3123 ≤ 2682423853737^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288787393 10000000000 2682423853737 6250000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336655687/625000000 : ℝ)^4147 ≤ (21987400474677/50000000000000 : ℝ)^3123 := by
    have hnat : (336655687 : ℕ)^4147*50000000000000^3123 ≤ 21987400474677^3123*625000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336655687 625000000 21987400474677 50000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270588729/1250000000 : ℝ)^4147 ≤ (13106417374417/100000000000000 : ℝ)^3123 := by
    have hnat : (270588729 : ℕ)^4147*100000000000000^3123 ≤ 13106417374417^3123*1250000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270588729 1250000000 13106417374417 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288787393/10000000000 : ℝ), (336655687/625000000 : ℝ), (-270588729/1250000000 : ℝ)] ![(2682423853737/6250000000000 : ℝ), (21987400474677/50000000000000 : ℝ), (13106417374417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288787393/10000000000 : ℝ)|^4147 ≤ (2682423853737/6250000000000 : ℝ)^3123
        have hw : |(5288787393/10000000000 : ℝ)|=(5288787393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336655687/625000000 : ℝ)|^4147 ≤ (21987400474677/50000000000000 : ℝ)^3123
        have hw : |(336655687/625000000 : ℝ)|=(336655687/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-270588729/1250000000 : ℝ)|^4147 ≤ (13106417374417/100000000000000 : ℝ)^3123
        have hw : |(-270588729/1250000000 : ℝ)|=(270588729/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_11 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4499777307/10000000000 : ℝ)*x 0 + (861566651/2000000000 : ℝ)*x 1 + (1076958369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4499777307/10000000000 : ℝ)^4147 ≤ (34631864794741/100000000000000 : ℝ)^3123 := by
    have hnat : (4499777307 : ℕ)^4147*100000000000000^3123 ≤ 34631864794741^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499777307 10000000000 34631864794741 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861566651/2000000000 : ℝ)^4147 ≤ (32684066483651/100000000000000 : ℝ)^3123 := by
    have hnat : (861566651 : ℕ)^4147*100000000000000^3123 ≤ 32684066483651^3123*2000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861566651 2000000000 32684066483651 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076958369/2500000000 : ℝ)^4147 ≤ (8171017177549/25000000000000 : ℝ)^3123 := by
    have hnat : (1076958369 : ℕ)^4147*25000000000000^3123 ≤ 8171017177549^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076958369 2500000000 8171017177549 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4499777307/10000000000 : ℝ), (861566651/2000000000 : ℝ), (1076958369/2500000000 : ℝ)] ![(34631864794741/100000000000000 : ℝ), (32684066483651/100000000000000 : ℝ), (8171017177549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4499777307/10000000000 : ℝ)|^4147 ≤ (34631864794741/100000000000000 : ℝ)^3123
        have hw : |(4499777307/10000000000 : ℝ)|=(4499777307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(861566651/2000000000 : ℝ)|^4147 ≤ (32684066483651/100000000000000 : ℝ)^3123
        have hw : |(861566651/2000000000 : ℝ)|=(861566651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076958369/2500000000 : ℝ)|^4147 ≤ (8171017177549/25000000000000 : ℝ)^3123
        have hw : |(1076958369/2500000000 : ℝ)|=(1076958369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_12 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-528154669/2500000000 : ℝ)*x 0 + (217639413/400000000 : ℝ)*x 1 + (5272576813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528154669/2500000000 : ℝ)^4147 ≤ (50757100257/400000000000 : ℝ)^3123 := by
    have hnat : (528154669 : ℕ)^4147*400000000000^3123 ≤ 50757100257^3123*2500000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528154669 2500000000 50757100257 400000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217639413/400000000 : ℝ)^4147 ≤ (5570817365463/12500000000000 : ℝ)^3123 := by
    have hnat : (217639413 : ℕ)^4147*12500000000000^3123 ≤ 5570817365463^3123*400000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217639413 400000000 5570817365463 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5272576813/10000000000 : ℝ)^4147 ≤ (42744186001033/100000000000000 : ℝ)^3123 := by
    have hnat : (5272576813 : ℕ)^4147*100000000000000^3123 ≤ 42744186001033^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272576813 10000000000 42744186001033 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-528154669/2500000000 : ℝ), (217639413/400000000 : ℝ), (5272576813/10000000000 : ℝ)] ![(50757100257/400000000000 : ℝ), (5570817365463/12500000000000 : ℝ), (42744186001033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-528154669/2500000000 : ℝ)|^4147 ≤ (50757100257/400000000000 : ℝ)^3123
        have hw : |(-528154669/2500000000 : ℝ)|=(528154669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217639413/400000000 : ℝ)|^4147 ≤ (5570817365463/12500000000000 : ℝ)^3123
        have hw : |(217639413/400000000 : ℝ)|=(217639413/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5272576813/10000000000 : ℝ)|^4147 ≤ (42744186001033/100000000000000 : ℝ)^3123
        have hw : |(5272576813/10000000000 : ℝ)|=(5272576813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_13 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369343071/10000000000 : ℝ)*x 0 + (-2209385181/10000000000 : ℝ)*x 1 + (2636288577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369343071/10000000000 : ℝ)^4147 ≤ (10947250357977/25000000000000 : ℝ)^3123 := by
    have hnat : (5369343071 : ℕ)^4147*25000000000000^3123 ≤ 10947250357977^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369343071 10000000000 10947250357977 25000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2209385181/10000000000 : ℝ)^4147 ≤ (13466808884027/100000000000000 : ℝ)^3123 := by
    have hnat : (2209385181 : ℕ)^4147*100000000000000^3123 ≤ 13466808884027^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209385181 10000000000 13466808884027 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2636288577/5000000000 : ℝ)^4147 ≤ (42744189671917/100000000000000 : ℝ)^3123 := by
    have hnat : (2636288577 : ℕ)^4147*100000000000000^3123 ≤ 42744189671917^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636288577 5000000000 42744189671917 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369343071/10000000000 : ℝ), (-2209385181/10000000000 : ℝ), (2636288577/5000000000 : ℝ)] ![(10947250357977/25000000000000 : ℝ), (13466808884027/100000000000000 : ℝ), (42744189671917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369343071/10000000000 : ℝ)|^4147 ≤ (10947250357977/25000000000000 : ℝ)^3123
        have hw : |(5369343071/10000000000 : ℝ)|=(5369343071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2209385181/10000000000 : ℝ)|^4147 ≤ (13466808884027/100000000000000 : ℝ)^3123
        have hw : |(-2209385181/10000000000 : ℝ)|=(2209385181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2636288577/5000000000 : ℝ)|^4147 ≤ (42744189671917/100000000000000 : ℝ)^3123
        have hw : |(2636288577/5000000000 : ℝ)|=(2636288577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_14 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369343389/10000000000 : ℝ)*x 0 + (5272576947/10000000000 : ℝ)*x 1 + (-220938503/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369343389/10000000000 : ℝ)^4147 ≤ (43789004875669/100000000000000 : ℝ)^3123 := by
    have hnat : (5369343389 : ℕ)^4147*100000000000000^3123 ≤ 43789004875669^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369343389 10000000000 43789004875669 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5272576947/10000000000 : ℝ)^4147 ≤ (42744187443551/100000000000000 : ℝ)^3123 := by
    have hnat : (5272576947 : ℕ)^4147*100000000000000^3123 ≤ 42744187443551^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5272576947 10000000000 42744187443551 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220938503/1000000000 : ℝ)^4147 ≤ (2693361532371/20000000000000 : ℝ)^3123 := by
    have hnat : (220938503 : ℕ)^4147*20000000000000^3123 ≤ 2693361532371^3123*1000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220938503 1000000000 2693361532371 20000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369343389/10000000000 : ℝ), (5272576947/10000000000 : ℝ), (-220938503/1000000000 : ℝ)] ![(43789004875669/100000000000000 : ℝ), (42744187443551/100000000000000 : ℝ), (2693361532371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369343389/10000000000 : ℝ)|^4147 ≤ (43789004875669/100000000000000 : ℝ)^3123
        have hw : |(5369343389/10000000000 : ℝ)|=(5369343389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5272576947/10000000000 : ℝ)|^4147 ≤ (42744187443551/100000000000000 : ℝ)^3123
        have hw : |(5272576947/10000000000 : ℝ)|=(5272576947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220938503/1000000000 : ℝ)|^4147 ≤ (2693361532371/20000000000000 : ℝ)^3123
        have hw : |(-220938503/1000000000 : ℝ)|=(220938503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1101_box_15 (p : ℝ) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121952731/5000000000 : ℝ)*x 0 + (4435766583/10000000000 : ℝ)*x 1 + (4435766749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121952731/5000000000 : ℝ)^4147 ≤ (32041574776827/100000000000000 : ℝ)^3123 := by
    have hnat : (2121952731 : ℕ)^4147*100000000000000^3123 ≤ 32041574776827^3123*5000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121952731 5000000000 32041574776827 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4435766583/10000000000 : ℝ)^4147 ≤ (4247401470057/12500000000000 : ℝ)^3123 := by
    have hnat : (4435766583 : ℕ)^4147*12500000000000^3123 ≤ 4247401470057^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435766583 10000000000 4247401470057 12500000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4435766749/10000000000 : ℝ)^4147 ≤ (33979213449009/100000000000000 : ℝ)^3123 := by
    have hnat : (4435766749 : ℕ)^4147*100000000000000^3123 ≤ 33979213449009^3123*10000000000^4147 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435766749 10000000000 33979213449009 100000000000000 4147 3123 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4147/1024 : ℝ)) 4147 3123 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121952731/5000000000 : ℝ), (4435766583/10000000000 : ℝ), (4435766749/10000000000 : ℝ)] ![(32041574776827/100000000000000 : ℝ), (4247401470057/12500000000000 : ℝ), (33979213449009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121952731/5000000000 : ℝ)|^4147 ≤ (32041574776827/100000000000000 : ℝ)^3123
        have hw : |(2121952731/5000000000 : ℝ)|=(2121952731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4435766583/10000000000 : ℝ)|^4147 ≤ (4247401470057/12500000000000 : ℝ)^3123
        have hw : |(4435766583/10000000000 : ℝ)|=(4435766583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4435766749/10000000000 : ℝ)|^4147 ≤ (33979213449009/100000000000000 : ℝ)^3123
        have hw : |(4435766749/10000000000 : ℝ)|=(4435766749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1101_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62227/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59267/100000 : ℝ) ∧ (39841/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (10379/12500 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (113/1000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1753/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (113/1000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1753/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (113/1000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (113/1000 : ℝ) ^ (8293/2048 : ℝ) ≤ (3660623087193239/25000000000000000000 : ℝ) := by
    have hpowers : (113/1000 : ℝ)^8293 ≤ (3660623087193239/25000000000000000000 : ℝ)^2048 := by
      have hnat : (113 : ℕ)^8293*25000000000000000000^2048 ≤ 3660623087193239^2048*1000^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        113 1000 3660623087193239 25000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (113/1000 : ℝ)) (X := (3660623087193239/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1753/12500 : ℝ) ^ (8293/2048 : ℝ) ≤ (35108671848353113/100000000000000000000 : ℝ) := by
    have hpowers : (1753/12500 : ℝ)^8293 ≤ (35108671848353113/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1753 : ℕ)^8293*100000000000000000000^2048 ≤ 35108671848353113^2048*12500^8293 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753 12500 35108671848353113 100000000000000000000 8293 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1753/12500 : ℝ)) (X := (35108671848353113/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503660623087193239/12500000000000000000 : ℝ) ≤ (2000144625676127/2000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (12503660623087193239/12500000000000000000 : ℝ)^2048 ≤ (2000144625676127/2000000000000000 : ℝ)^8293 := by
      have hnat : (12503660623087193239 : ℕ)^2048*2000000000000000^8293 ≤ 2000144625676127^8293*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503660623087193239 12500000000000000000 2000144625676127 2000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000144625676127/2000000000000000 : ℝ)) (X := (12503660623087193239/12500000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049751164197126069/100000000000000000000 : ℝ) ≤ (2500307100275177/2500000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (100049751164197126069/100000000000000000000 : ℝ)^2048 ≤ (2500307100275177/2500000000000000 : ℝ)^8293 := by
      have hnat : (100049751164197126069 : ℕ)^2048*2500000000000000^8293 ≤ 2500307100275177^8293*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049751164197126069 100000000000000000000 2500307100275177 2500000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500307100275177/2500000000000000 : ℝ)) (X := (100049751164197126069/100000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035108671848353113/50000000000000000000 : ℝ) ≤ (10001733673820781/10000000000000000 : ℝ) ^ (8293/2048 : ℝ) := by
    have hpowers : (50035108671848353113/50000000000000000000 : ℝ)^2048 ≤ (10001733673820781/10000000000000000 : ℝ)^8293 := by
      have hnat : (50035108671848353113 : ℕ)^2048*10000000000000000^8293 ≤ 10001733673820781^8293*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035108671848353113 50000000000000000000 10001733673820781 10000000000000000 2048 8293 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001733673820781/10000000000000000 : ℝ)) (X := (50035108671848353113/50000000000000000000 : ℝ)) (by norm_num) 8293 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3660623087193239/25000000000000000000 : ℝ) ≤ ((1361527531911759997/1362000000000000000 : ℝ)+2*(505272720073/272400000000000 : ℝ)*(113/1000 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (1361527531911759997/1362000000000000000 : ℝ)+2*(505272720073/272400000000000 : ℝ)*(113/1000 : ℝ)=(2000144625676127/2000000000000000 : ℝ) by norm_num, show 1+2*(3660623087193239/25000000000000000000 : ℝ)=(12503660623087193239/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35108671848353113/100000000000000000000 : ℝ)+(3660623087193239/25000000000000000000 : ℝ) ≤ ((1361527531911759997/1362000000000000000 : ℝ)+(505272720073/272400000000000 : ℝ)*((1753/12500 : ℝ)+(113/1000 : ℝ)))^(8293/2048 : ℝ) := by
    rw [show (1361527531911759997/1362000000000000000 : ℝ)+(505272720073/272400000000000 : ℝ)*((1753/12500 : ℝ)+(113/1000 : ℝ))=(2500307100275177/2500000000000000 : ℝ) by norm_num, show 1+(35108671848353113/100000000000000000000 : ℝ)+(3660623087193239/25000000000000000000 : ℝ)=(100049751164197126069/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35108671848353113/100000000000000000000 : ℝ) ≤ ((1361527531911759997/1362000000000000000 : ℝ)+2*(505272720073/272400000000000 : ℝ)*(1753/12500 : ℝ))^(8293/2048 : ℝ) := by
    rw [show (1361527531911759997/1362000000000000000 : ℝ)+2*(505272720073/272400000000000 : ℝ)*(1753/12500 : ℝ)=(10001733673820781/10000000000000000 : ℝ) by norm_num, show 1+2*(35108671848353113/100000000000000000000 : ℝ)=(50035108671848353113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1361527531911759997/1362000000000000000 : ℝ)*(X 1 0+X 2 0)+(505272720073/272400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (1361527531911759997/1362000000000000000 : ℝ)) (alpha := (505272720073/272400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1361527531911759997/1362000000000000000 : ℝ)*(X 0 1+X 2 1)+(505272720073/272400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (1361527531911759997/1362000000000000000 : ℝ)) (alpha := (505272720073/272400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1361527531911759997/1362000000000000000 : ℝ)*(X 0 2+X 1 2)+(505272720073/272400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8293/2048 : ℝ)) (lo := (113/1000 : ℝ)) (hi := (1753/12500 : ℝ)) (c := (1361527531911759997/1362000000000000000 : ℝ)) (alpha := (505272720073/272400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2058389551/10000000000 : ℝ)*X 0 0+(336055391/625000000 : ℝ)*X 0 1+(5376886337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((661947871/1250000000 : ℝ)*X 1 0+(-542136403/2500000000 : ℝ)*X 1 1+(2688443151/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5295582857/10000000000 : ℝ)*X 2 0+(33605539/62500000 : ℝ)*X 2 1+(-542136461/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((895694549/2000000000 : ℝ)*X 0 0+(2159312969/5000000000 : ℝ)*X 0 1+(539828301/1250000000 : ℝ)*X 0 2+(895694549/2000000000 : ℝ)*X 1 0+(2159312969/5000000000 : ℝ)*X 1 1+(539828301/1250000000 : ℝ)*X 1 2+(895694549/2000000000 : ℝ)*X 2 0+(2159312969/5000000000 : ℝ)*X 2 1+(539828301/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1158148739/5000000000 : ℝ)*X 0 0+(2640297961/5000000000 : ℝ)*X 0 1+(1056119173/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363675059/10000000000 : ℝ)*X 1 0+(-2206299143/10000000000 : ℝ)*X 1 1+(5280595829/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2681837553/5000000000 : ℝ)*X 2 0+(5280595927/10000000000 : ℝ)*X 2 1+(-2206298949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((852430209/2000000000 : ℝ)*X 0 0+(885353159/2000000000 : ℝ)*X 0 1+(4426765919/10000000000 : ℝ)*X 0 2+(852430209/2000000000 : ℝ)*X 1 0+(885353159/2000000000 : ℝ)*X 1 1+(4426765919/10000000000 : ℝ)*X 1 2+(852430209/2000000000 : ℝ)*X 2 0+(885353159/2000000000 : ℝ)*X 2 1+(4426765919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1131206817/5000000000 : ℝ)*X 0 0+(1043037749/2000000000 : ℝ)*X 0 1+(2693245509/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288787277/10000000000 : ℝ)*X 1 0+(-2164710103/10000000000 : ℝ)*X 1 1+(2693245453/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288787393/10000000000 : ℝ)*X 2 0+(336655687/625000000 : ℝ)*X 2 1+(-270588729/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4499777307/10000000000 : ℝ)*X 0 0+(861566651/2000000000 : ℝ)*X 0 1+(1076958369/2500000000 : ℝ)*X 0 2+(4499777307/10000000000 : ℝ)*X 1 0+(861566651/2000000000 : ℝ)*X 1 1+(1076958369/2500000000 : ℝ)*X 1 2+(4499777307/10000000000 : ℝ)*X 2 0+(861566651/2000000000 : ℝ)*X 2 1+(1076958369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-528154669/2500000000 : ℝ)*X 0 0+(217639413/400000000 : ℝ)*X 0 1+(5272576813/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369343071/10000000000 : ℝ)*X 1 0+(-2209385181/10000000000 : ℝ)*X 1 1+(2636288577/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369343389/10000000000 : ℝ)*X 2 0+(5272576947/10000000000 : ℝ)*X 2 1+(-220938503/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2121952731/5000000000 : ℝ)*X 0 0+(4435766583/10000000000 : ℝ)*X 0 1+(4435766749/10000000000 : ℝ)*X 0 2+(2121952731/5000000000 : ℝ)*X 1 0+(4435766583/10000000000 : ℝ)*X 1 1+(4435766749/10000000000 : ℝ)*X 1 2+(2121952731/5000000000 : ℝ)*X 2 0+(4435766583/10000000000 : ℝ)*X 2 1+(4435766749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1101_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62227/100000 : ℝ) ≤ (-14124942796661558423029649311457/22700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27300461/50000000000000 : ℝ)*(upper0) + (9778697/50000000000000 : ℝ)*(lower1) + (99073361/100000000000000 : ℝ)*(lower2) + (17777599/100000000000000 : ℝ)*(lower3) + (3886215408583819/100000000000000 : ℝ)*(major0) + (3886215408583819/100000000000000 : ℝ)*(major1) + (3886215408583819/100000000000000 : ℝ)*(major2) + (1962311571/50000000000000 : ℝ)*(sp1) + (5179260029484141/100000000000000 : ℝ)*(sp4) + (323703609044601/6250000000000 : ℝ)*(sp5) + (1035835394964197/20000000000000 : ℝ)*(sp6) + (1306955310183173/50000000000000 : ℝ)*(sp7) + (1639852617/100000000000000 : ℝ)*(sp8) + (84694515773/100000000000000 : ℝ)*(sp14) + (1306955310183173/50000000000000 : ℝ)*(f.failure) + (2589630834668379/50000000000000 : ℝ)*(f.sum) + (204047324719493/13620000000000000000000000000 : ℝ)*base66 + (673680633258819/45400000000000000000000000000000 : ℝ)*base68 + (51609271216458819/45400000000000000000000000000000 : ℝ)*base70 + (93881960228541181/45400000000000000000000000000000 : ℝ)*base71 + (289719950616427/13620000000000000000000000000 : ℝ)*base73 + (270398112672258819/45400000000000000000000000000000 : ℝ)*base76 + (1522441751290741181/45400000000000000000000000000000 : ℝ)*base77 + (1391155119071858819/45400000000000000000000000000000 : ℝ)*base80 + (107338780860007/13620000000000000000000000000 : ℝ)*base81 + (889613/250000000000000000000 : ℝ)*base90 + (889613/250000000000000000000 : ℝ)*base92 + (889613/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59267/100000 : ℝ) ≤ (13454198589591877775042292411923/22700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5299123/10000000000000 : ℝ)*(lower1) + (5186397/4000000000000 : ℝ)*(upper2) + (162213/1000000000000 : ℝ)*(lower4) + (3949702316409359/100000000000000 : ℝ)*(major0) + (3949702316409359/100000000000000 : ℝ)*(major1) + (3949702316409359/100000000000000 : ℝ)*(major2) + (5223024382589707/100000000000000 : ℝ)*(sp0) + (1305757714675473/25000000000000 : ℝ)*(sp1) + (2611476309820007/50000000000000 : ℝ)*(sp2) + (1328305121598357/50000000000000 : ℝ)*(sp3) + (231937447/5000000000000 : ℝ)*(sp5) + (1179867087/50000000000000 : ℝ)*(sp7) + (41438905409/50000000000000 : ℝ)*(sp10) + (2778715281/25000000000000 : ℝ)*(sp12) + (332076575366361/12500000000000 : ℝ)*(f.failure) + (326439718590677/6250000000000 : ℝ)*(f.sum) + (70036228958773/13620000000000000000000000000 : ℝ)*base66 + (297331820404615641/45400000000000000000000000000000 : ℝ)*base67 + (8653825444384359/45400000000000000000000000000000 : ℝ)*base70 + (54936600614184359/45400000000000000000000000000000 : ℝ)*base72 + (25242190131647/13620000000000000000000000000 : ℝ)*base73 + (307195307658584359/45400000000000000000000000000000 : ℝ)*base76 + (736926073456584359/45400000000000000000000000000000 : ℝ)*base78 + (1560512215015641/45400000000000000000000000000000 : ℝ)*base79 + (21973593233087/13620000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (351559/62500000000000000000 : ℝ)*base89 + (351559/62500000000000000000 : ℝ)*base91 + (351559/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39841/50000 : ℝ) ≤ (4522081699743477063742612185771/5675000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55064153/100000000000000 : ℝ)*(upper0) + (10197437/50000000000000 : ℝ)*(lower1) + (27997973/25000000000000 : ℝ)*(lower3) + (33058403/25000000000000 : ℝ)*(upper4) + (2208922706997243/50000000000000 : ℝ)*(major0) + (2208922706997243/50000000000000 : ℝ)*(major1) + (2208922706997243/50000000000000 : ℝ)*(major2) + (13647343017/50000000000000 : ℝ)*(sp1) + (122236875661/100000000000000 : ℝ)*(sp2) + (9143830567/10000000000000 : ℝ)*(sp3) + (5837638682073751/100000000000000 : ℝ)*(sp8) + (5837611387387717/100000000000000 : ℝ)*(sp9) + (583751644519809/10000000000000 : ℝ)*(sp10) + (742849821983527/25000000000000 : ℝ)*(sp11) + (1485745363119889/50000000000000 : ℝ)*(f.failure) + (5837638682073751/100000000000000 : ℝ)*(f.sum) + (7154359762473/2270000000000000000000000000 : ℝ)*base65 + (21854081986372243/22700000000000000000000000000000 : ℝ)*base68 + (47011102542072243/22700000000000000000000000000000 : ℝ)*base70 + (84261701322772243/22700000000000000000000000000000 : ℝ)*base72 + (3291927138843/2270000000000000000000000000 : ℝ)*base73 + (22295644167527757/22700000000000000000000000000000 : ℝ)*base75 + (150506596622972243/22700000000000000000000000000000 : ℝ)*base78 + (162305279533872243/22700000000000000000000000000000 : ℝ)*base80 + (4736079186167/2270000000000000000000000000 : ℝ)*base82 + (3137191/250000000000000000000 : ℝ)*base89 + (3137191/250000000000000000000 : ℝ)*base91 + (3137191/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-10379/12500 : ℝ) ≤ (-2355964051139034696741058369961/2837500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93224737/100000000000000 : ℝ)*(lower2) + (14774289/100000000000000 : ℝ)*(upper3) + (206201917/100000000000000 : ℝ)*(upper5) + (556570051837487/12500000000000 : ℝ)*(major0) + (556570051837487/12500000000000 : ℝ)*(major1) + (556570051837487/12500000000000 : ℝ)*(major2) + (460603283/5000000000000 : ℝ)*(sp0) + (168661820767/100000000000000 : ℝ)*(sp6) + (65997017191/100000000000000 : ℝ)*(sp7) + (2010711147/25000000000000 : ℝ)*(sp8) + (5937939685736963/100000000000000 : ℝ)*(sp12) + (5937956940647211/100000000000000 : ℝ)*(sp13) + (1484447069706611/25000000000000 : ℝ)*(sp14) + (187173400943549/6250000000000 : ℝ)*(sp15) + (1497420206056987/50000000000000 : ℝ)*(f.failure) + (5937956940647211/100000000000000 : ℝ)*(f.sum) + (21874821562913/3405000000000000000000000000 : ℝ)*base66 + (47177628125812487/5675000000000000000000000000000 : ℝ)*base68 + (13946166041112487/5675000000000000000000000000000 : ℝ)*base70 + (12185006400587513/5675000000000000000000000000000 : ℝ)*base71 + (467910617779/106406250000000000000000000 : ℝ)*base74 + (11428004218462513/5675000000000000000000000000000 : ℝ)*base75 + (20294040309387487/5675000000000000000000000000000 : ℝ)*base78 + (3106732886162487/5675000000000000000000000000000 : ℝ)*base80 + (56845550081/106406250000000000000000000 : ℝ)*base81 + (655347/250000000000000000000 : ℝ)*base90 + (655347/250000000000000000000 : ℝ)*base92 + (655347/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1101_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (113/1000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59267/100000 : ℝ) else (39841/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10379/12500 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1101_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1101_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59267/100000 : ℝ) else (39841/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10379/12500 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1101_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1101_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8293/2048 : ℝ) ≤ p) (hpb : p ≤ (4147/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7433719/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1753/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11299/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62227/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59267/100000 : ℝ) else (39841/50000 : ℝ) ≤ X j i ∧ X j i ≤ (10379/12500 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1101_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
