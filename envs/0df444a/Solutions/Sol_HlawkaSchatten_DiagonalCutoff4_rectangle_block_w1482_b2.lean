-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1482_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:00.391952+00:00
-- url     : https://prove2.me/submissions/8920deaa-a8e8-4413-a792-70b270f45c3b

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
theorem support_rectangle_w1482_s6_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-956631541/5000000000 : ℝ)*x 0 + (5437166723/10000000000 : ℝ)*x 1 + (5215969617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956631541/5000000000 : ℝ)^4461 ≤ (2922340286619/25000000000000 : ℝ)^3437 := by
    have hnat : (956631541 : ℕ)^4461*25000000000000^3437 ≤ 2922340286619^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956631541 5000000000 2922340286619 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437166723/10000000000 : ℝ)^4461 ≤ (1133629422693/2500000000000 : ℝ)^3437 := by
    have hnat : (5437166723 : ℕ)^4461*2500000000000^3437 ≤ 1133629422693^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437166723 10000000000 1133629422693 2500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215969617/10000000000 : ℝ)^4461 ≤ (42965461935291/100000000000000 : ℝ)^3437 := by
    have hnat : (5215969617 : ℕ)^4461*100000000000000^3437 ≤ 42965461935291^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215969617 10000000000 42965461935291 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-956631541/5000000000 : ℝ), (5437166723/10000000000 : ℝ), (5215969617/10000000000 : ℝ)] ![(2922340286619/25000000000000 : ℝ), (1133629422693/2500000000000 : ℝ), (42965461935291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-956631541/5000000000 : ℝ)|^4461 ≤ (2922340286619/25000000000000 : ℝ)^3437
        have hw : |(-956631541/5000000000 : ℝ)|=(956631541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437166723/10000000000 : ℝ)|^4461 ≤ (1133629422693/2500000000000 : ℝ)^3437
        have hw : |(5437166723/10000000000 : ℝ)|=(5437166723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215969617/10000000000 : ℝ)|^4461 ≤ (42965461935291/100000000000000 : ℝ)^3437
        have hw : |(5215969617/10000000000 : ℝ)|=(5215969617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s6_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267660291/500000000 : ℝ)*x 0 + (-2026620701/10000000000 : ℝ)*x 1 + (5215969623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267660291/500000000 : ℝ)^4461 ≤ (44438433478153/100000000000000 : ℝ)^3437 := by
    have hnat : (267660291 : ℕ)^4461*100000000000000^3437 ≤ 44438433478153^3437*500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267660291 500000000 44438433478153 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2026620701/10000000000 : ℝ)^4461 ≤ (6298052250781/50000000000000 : ℝ)^3437 := by
    have hnat : (2026620701 : ℕ)^4461*50000000000000^3437 ≤ 6298052250781^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026620701 10000000000 6298052250781 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215969623/10000000000 : ℝ)^4461 ≤ (537068274993/1250000000000 : ℝ)^3437 := by
    have hnat : (5215969623 : ℕ)^4461*1250000000000^3437 ≤ 537068274993^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215969623 10000000000 537068274993 1250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267660291/500000000 : ℝ), (-2026620701/10000000000 : ℝ), (5215969623/10000000000 : ℝ)] ![(44438433478153/100000000000000 : ℝ), (6298052250781/50000000000000 : ℝ), (537068274993/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267660291/500000000 : ℝ)|^4461 ≤ (44438433478153/100000000000000 : ℝ)^3437
        have hw : |(267660291/500000000 : ℝ)|=(267660291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2026620701/10000000000 : ℝ)|^4461 ≤ (6298052250781/50000000000000 : ℝ)^3437
        have hw : |(-2026620701/10000000000 : ℝ)|=(2026620701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215969623/10000000000 : ℝ)|^4461 ≤ (537068274993/1250000000000 : ℝ)^3437
        have hw : |(5215969623/10000000000 : ℝ)|=(5215969623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s6_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26766029/50000000 : ℝ)*x 0 + (162999051/312500000 : ℝ)*x 1 + (-506655179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26766029/50000000 : ℝ)^4461 ≤ (44438433262663/100000000000000 : ℝ)^3437 := by
    have hnat : (26766029 : ℕ)^4461*100000000000000^3437 ≤ 44438433262663^3437*50000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26766029 50000000 44438433262663 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162999051/312500000 : ℝ)^4461 ≤ (42965462095663/100000000000000 : ℝ)^3437 := by
    have hnat : (162999051 : ℕ)^4461*100000000000000^3437 ≤ 42965462095663^3437*312500000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162999051 312500000 42965462095663 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506655179/2500000000 : ℝ)^4461 ≤ (1574513077821/12500000000000 : ℝ)^3437 := by
    have hnat : (506655179 : ℕ)^4461*12500000000000^3437 ≤ 1574513077821^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506655179 2500000000 1574513077821 12500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26766029/50000000 : ℝ), (162999051/312500000 : ℝ), (-506655179/2500000000 : ℝ)] ![(44438433262663/100000000000000 : ℝ), (42965462095663/100000000000000 : ℝ), (1574513077821/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26766029/50000000 : ℝ)|^4461 ≤ (44438433262663/100000000000000 : ℝ)^3437
        have hw : |(26766029/50000000 : ℝ)|=(26766029/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(162999051/312500000 : ℝ)|^4461 ≤ (42965462095663/100000000000000 : ℝ)^3437
        have hw : |(162999051/312500000 : ℝ)|=(162999051/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506655179/2500000000 : ℝ)|^4461 ≤ (1574513077821/12500000000000 : ℝ)^3437
        have hw : |(-506655179/2500000000 : ℝ)|=(506655179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s6_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283950313/10000000000 : ℝ)*x 0 + (808915093/2000000000 : ℝ)*x 1 + (2267787007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283950313/10000000000 : ℝ)^4461 ≤ (8319520198573/25000000000000 : ℝ)^3437 := by
    have hnat : (4283950313 : ℕ)^4461*25000000000000^3437 ≤ 8319520198573^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283950313 10000000000 8319520198573 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (808915093/2000000000 : ℝ)^4461 ≤ (30884951958989/100000000000000 : ℝ)^3437 := by
    have hnat : (808915093 : ℕ)^4461*100000000000000^3437 ≤ 30884951958989^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      808915093 2000000000 30884951958989 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267787007/5000000000 : ℝ)^4461 ≤ (35836967228459/100000000000000 : ℝ)^3437 := by
    have hnat : (2267787007 : ℕ)^4461*100000000000000^3437 ≤ 35836967228459^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267787007 5000000000 35836967228459 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283950313/10000000000 : ℝ), (808915093/2000000000 : ℝ), (2267787007/5000000000 : ℝ)] ![(8319520198573/25000000000000 : ℝ), (30884951958989/100000000000000 : ℝ), (35836967228459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283950313/10000000000 : ℝ)|^4461 ≤ (8319520198573/25000000000000 : ℝ)^3437
        have hw : |(4283950313/10000000000 : ℝ)|=(4283950313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(808915093/2000000000 : ℝ)|^4461 ≤ (30884951958989/100000000000000 : ℝ)^3437
        have hw : |(808915093/2000000000 : ℝ)|=(808915093/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2267787007/5000000000 : ℝ)|^4461 ≤ (35836967228459/100000000000000 : ℝ)^3437
        have hw : |(2267787007/5000000000 : ℝ)|=(2267787007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s6_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-239161669/1250000000 : ℝ)*x 0 + (1043420327/2000000000 : ℝ)*x 1 + (5436026379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239161669/1250000000 : ℝ)^4461 ≤ (1461200148213/12500000000000 : ℝ)^3437 := by
    have hnat : (239161669 : ℕ)^4461*12500000000000^3437 ≤ 1461200148213^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239161669 1250000000 1461200148213 12500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043420327/2000000000 : ℝ)^4461 ≤ (42977565254739/100000000000000 : ℝ)^3437 := by
    have hnat : (1043420327 : ℕ)^4461*100000000000000^3437 ≤ 42977565254739^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043420327 2000000000 42977565254739 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436026379/10000000000 : ℝ)^4461 ≤ (11333208386517/25000000000000 : ℝ)^3437 := by
    have hnat : (5436026379 : ℕ)^4461*25000000000000^3437 ≤ 11333208386517^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436026379 10000000000 11333208386517 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-239161669/1250000000 : ℝ), (1043420327/2000000000 : ℝ), (5436026379/10000000000 : ℝ)] ![(1461200148213/12500000000000 : ℝ), (42977565254739/100000000000000 : ℝ), (11333208386517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-239161669/1250000000 : ℝ)|^4461 ≤ (1461200148213/12500000000000 : ℝ)^3437
        have hw : |(-239161669/1250000000 : ℝ)|=(239161669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043420327/2000000000 : ℝ)|^4461 ≤ (42977565254739/100000000000000 : ℝ)^3437
        have hw : |(1043420327/2000000000 : ℝ)|=(1043420327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436026379/10000000000 : ℝ)|^4461 ≤ (11333208386517/25000000000000 : ℝ)^3437
        have hw : |(5436026379/10000000000 : ℝ)|=(5436026379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s6_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295417599/10000000000 : ℝ)*x 0 + (-361312791/2000000000 : ℝ)*x 1 + (5436026379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295417599/10000000000 : ℝ)^4461 ≤ (4381679758193/10000000000000 : ℝ)^3437 := by
    have hnat : (5295417599 : ℕ)^4461*10000000000000^3437 ≤ 4381679758193^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295417599 10000000000 4381679758193 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (361312791/2000000000 : ℝ)^4461 ≤ (1085036885203/10000000000000 : ℝ)^3437 := by
    have hnat : (361312791 : ℕ)^4461*10000000000000^3437 ≤ 1085036885203^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361312791 2000000000 1085036885203 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436026379/10000000000 : ℝ)^4461 ≤ (11333208386517/25000000000000 : ℝ)^3437 := by
    have hnat : (5436026379 : ℕ)^4461*25000000000000^3437 ≤ 11333208386517^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436026379 10000000000 11333208386517 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295417599/10000000000 : ℝ), (-361312791/2000000000 : ℝ), (5436026379/10000000000 : ℝ)] ![(4381679758193/10000000000000 : ℝ), (1085036885203/10000000000000 : ℝ), (11333208386517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295417599/10000000000 : ℝ)|^4461 ≤ (4381679758193/10000000000000 : ℝ)^3437
        have hw : |(5295417599/10000000000 : ℝ)|=(5295417599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-361312791/2000000000 : ℝ)|^4461 ≤ (1085036885203/10000000000000 : ℝ)^3437
        have hw : |(-361312791/2000000000 : ℝ)|=(361312791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436026379/10000000000 : ℝ)|^4461 ≤ (11333208386517/25000000000000 : ℝ)^3437
        have hw : |(5436026379/10000000000 : ℝ)|=(5436026379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s6_6 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (827409/1562500 : ℝ)*x 0 + (5436026379/10000000000 : ℝ)*x 1 + (-361312791/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827409/1562500 : ℝ)^4461 ≤ (43816797592669/100000000000000 : ℝ)^3437 := by
    have hnat : (827409 : ℕ)^4461*100000000000000^3437 ≤ 43816797592669^3437*1562500^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827409 1562500 43816797592669 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436026379/10000000000 : ℝ)^4461 ≤ (11333208386517/25000000000000 : ℝ)^3437 := by
    have hnat : (5436026379 : ℕ)^4461*25000000000000^3437 ≤ 11333208386517^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436026379 10000000000 11333208386517 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361312791/2000000000 : ℝ)^4461 ≤ (1085036885203/10000000000000 : ℝ)^3437 := by
    have hnat : (361312791 : ℕ)^4461*10000000000000^3437 ≤ 1085036885203^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361312791 2000000000 1085036885203 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827409/1562500 : ℝ), (5436026379/10000000000 : ℝ), (-361312791/2000000000 : ℝ)] ![(43816797592669/100000000000000 : ℝ), (11333208386517/25000000000000 : ℝ), (1085036885203/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827409/1562500 : ℝ)|^4461 ≤ (43816797592669/100000000000000 : ℝ)^3437
        have hw : |(827409/1562500 : ℝ)|=(827409/1562500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436026379/10000000000 : ℝ)|^4461 ≤ (11333208386517/25000000000000 : ℝ)^3437
        have hw : |(5436026379/10000000000 : ℝ)|=(5436026379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-361312791/2000000000 : ℝ)|^4461 ≤ (1085036885203/10000000000000 : ℝ)^3437
        have hw : |(-361312791/2000000000 : ℝ)|=(361312791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s6_7 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4284017497/10000000000 : ℝ)*x 0 + (4533061223/10000000000 : ℝ)*x 1 + (2023553359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4284017497/10000000000 : ℝ)^4461 ≤ (16639379087957/50000000000000 : ℝ)^3437 := by
    have hnat : (4284017497 : ℕ)^4461*50000000000000^3437 ≤ 16639379087957^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284017497 10000000000 16639379087957 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533061223/10000000000 : ℝ)^4461 ≤ (17905599866699/50000000000000 : ℝ)^3437 := by
    have hnat : (4533061223 : ℕ)^4461*50000000000000^3437 ≤ 17905599866699^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533061223 10000000000 17905599866699 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2023553359/5000000000 : ℝ)^4461 ≤ (30910042077617/100000000000000 : ℝ)^3437 := by
    have hnat : (2023553359 : ℕ)^4461*100000000000000^3437 ≤ 30910042077617^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2023553359 5000000000 30910042077617 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4284017497/10000000000 : ℝ), (4533061223/10000000000 : ℝ), (2023553359/5000000000 : ℝ)] ![(16639379087957/50000000000000 : ℝ), (17905599866699/50000000000000 : ℝ), (30910042077617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4284017497/10000000000 : ℝ)|^4461 ≤ (16639379087957/50000000000000 : ℝ)^3437
        have hw : |(4284017497/10000000000 : ℝ)|=(4284017497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533061223/10000000000 : ℝ)|^4461 ≤ (17905599866699/50000000000000 : ℝ)^3437
        have hw : |(4533061223/10000000000 : ℝ)|=(4533061223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2023553359/5000000000 : ℝ)|^4461 ≤ (30910042077617/100000000000000 : ℝ)^3437
        have hw : |(2023553359/5000000000 : ℝ)|=(2023553359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10793/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5397/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3869/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10793/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10793/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10793/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7739/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10793/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10793/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7739/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10793/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10793/100000 : ℝ) ^ (4459/1024 : ℝ) ≤ (6163468256442563/100000000000000000000 : ℝ) := by
    have hpowers : (10793/100000 : ℝ)^4459 ≤ (6163468256442563/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10793 : ℕ)^4459*100000000000000000000^1024 ≤ 6163468256442563^1024*100000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10793 100000 6163468256442563 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10793/100000 : ℝ)) (X := (6163468256442563/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7739/50000 : ℝ) ^ (4459/1024 : ℝ) ≤ (29622356974504999/100000000000000000000 : ℝ) := by
    have hpowers : (7739/50000 : ℝ)^4459 ≤ (29622356974504999/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7739 : ℕ)^4459*100000000000000000000^1024 ≤ 29622356974504999^1024*50000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7739 50000 29622356974504999 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7739/50000 : ℝ)) (X := (29622356974504999/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006163468256442563/50000000000000000000 : ℝ) ≤ (10000283072072167/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50006163468256442563/50000000000000000000 : ℝ)^1024 ≤ (10000283072072167/10000000000000000 : ℝ)^4459 := by
      have hnat : (50006163468256442563 : ℕ)^1024*10000000000000000^4459 ≤ 10000283072072167^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006163468256442563 50000000000000000000 10000283072072167 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283072072167/10000000000000000 : ℝ)) (X := (50006163468256442563/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017892912615473781/50000000000000000000 : ℝ) ≤ (2500205425179733/2500000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50017892912615473781/50000000000000000000 : ℝ)^1024 ≤ (2500205425179733/2500000000000000 : ℝ)^4459 := by
      have hnat : (50017892912615473781 : ℕ)^1024*2500000000000000^4459 ≤ 2500205425179733^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017892912615473781 50000000000000000000 2500205425179733 2500000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500205425179733/2500000000000000 : ℝ)) (X := (50017892912615473781/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029622356974504999/50000000000000000000 : ℝ) ≤ (10001360329365697/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50029622356974504999/50000000000000000000 : ℝ)^1024 ≤ (10001360329365697/10000000000000000 : ℝ)^4459 := by
      have hnat : (50029622356974504999 : ℕ)^1024*10000000000000000^4459 ≤ 10001360329365697^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029622356974504999 50000000000000000000 10001360329365697 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001360329365697/10000000000000000 : ℝ)) (X := (50029622356974504999/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6163468256442563/100000000000000000000 : ℝ) ≤ ((9367939870937806621/9370000000000000000 : ℝ)+2*(107725729353/93700000000000 : ℝ)*(10793/100000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (9367939870937806621/9370000000000000000 : ℝ)+2*(107725729353/93700000000000 : ℝ)*(10793/100000 : ℝ)=(10000283072072167/10000000000000000 : ℝ) by norm_num, show 1+2*(6163468256442563/100000000000000000000 : ℝ)=(50006163468256442563/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29622356974504999/100000000000000000000 : ℝ)+(6163468256442563/100000000000000000000 : ℝ) ≤ ((9367939870937806621/9370000000000000000 : ℝ)+(107725729353/93700000000000 : ℝ)*((7739/50000 : ℝ)+(10793/100000 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (9367939870937806621/9370000000000000000 : ℝ)+(107725729353/93700000000000 : ℝ)*((7739/50000 : ℝ)+(10793/100000 : ℝ))=(2500205425179733/2500000000000000 : ℝ) by norm_num, show 1+(29622356974504999/100000000000000000000 : ℝ)+(6163468256442563/100000000000000000000 : ℝ)=(50017892912615473781/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29622356974504999/100000000000000000000 : ℝ) ≤ ((9367939870937806621/9370000000000000000 : ℝ)+2*(107725729353/93700000000000 : ℝ)*(7739/50000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (9367939870937806621/9370000000000000000 : ℝ)+2*(107725729353/93700000000000 : ℝ)*(7739/50000 : ℝ)=(10001360329365697/10000000000000000 : ℝ) by norm_num, show 1+2*(29622356974504999/100000000000000000000 : ℝ)=(50029622356974504999/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9367939870937806621/9370000000000000000 : ℝ)*(X 1 0+X 2 0)+(107725729353/93700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (10793/100000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (9367939870937806621/9370000000000000000 : ℝ)) (alpha := (107725729353/93700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9367939870937806621/9370000000000000000 : ℝ)*(X 0 1+X 2 1)+(107725729353/93700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (10793/100000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (9367939870937806621/9370000000000000000 : ℝ)) (alpha := (107725729353/93700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9367939870937806621/9370000000000000000 : ℝ)*(X 0 2+X 1 2)+(107725729353/93700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (10793/100000 : ℝ)) (hi := (7739/50000 : ℝ)) (c := (9367939870937806621/9370000000000000000 : ℝ)) (alpha := (107725729353/93700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-956631541/5000000000 : ℝ)*X 0 0+(5437166723/10000000000 : ℝ)*X 0 1+(5215969617/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267660291/500000000 : ℝ)*X 1 0+(-2026620701/10000000000 : ℝ)*X 1 1+(5215969623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((26766029/50000000 : ℝ)*X 2 0+(162999051/312500000 : ℝ)*X 2 1+(-506655179/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283950313/10000000000 : ℝ)*X 0 0+(808915093/2000000000 : ℝ)*X 0 1+(2267787007/5000000000 : ℝ)*X 0 2+(4283950313/10000000000 : ℝ)*X 1 0+(808915093/2000000000 : ℝ)*X 1 1+(2267787007/5000000000 : ℝ)*X 1 2+(4283950313/10000000000 : ℝ)*X 2 0+(808915093/2000000000 : ℝ)*X 2 1+(2267787007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-239161669/1250000000 : ℝ)*X 0 0+(1043420327/2000000000 : ℝ)*X 0 1+(5436026379/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295417599/10000000000 : ℝ)*X 1 0+(-361312791/2000000000 : ℝ)*X 1 1+(5436026379/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((827409/1562500 : ℝ)*X 2 0+(5436026379/10000000000 : ℝ)*X 2 1+(-361312791/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4284017497/10000000000 : ℝ)*X 0 0+(4533061223/10000000000 : ℝ)*X 0 1+(2023553359/5000000000 : ℝ)*X 0 2+(4284017497/10000000000 : ℝ)*X 1 0+(4533061223/10000000000 : ℝ)*X 1 1+(2023553359/5000000000 : ℝ)*X 1 2+(4284017497/10000000000 : ℝ)*X 2 0+(4533061223/10000000000 : ℝ)*X 2 1+(2023553359/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13553519364242128431111/1171250000000000000000000000 : ℝ) := by norm_num
    linear_combination (64514807/3125000000000 : ℝ)*(base19) + (476498239/25000000000000 : ℝ)*(base23) + (15159247/20000000000000 : ℝ)*(lower2) + (74186041/25000000000000 : ℝ)*(upper3) + (175512233/100000000000000 : ℝ)*(upper5) + (1639403876573839/50000000000000 : ℝ)*(major0) + (1639403876573839/50000000000000 : ℝ)*(major1) + (1639403876573839/50000000000000 : ℝ)*(major2) + (14127775751427/312500000000 : ℝ)*(sp0) + (1130229423995957/25000000000000 : ℝ)*(sp1) + (565114731808087/12500000000000 : ℝ)*(sp2) + (2036679709517491/100000000000000 : ℝ)*(sp3) + (7880000253/25000000000000 : ℝ)*(sp4) + (3912648039/25000000000000 : ℝ)*(sp7) + (1018347680054823/50000000000000 : ℝ)*(f.failure) + (1130229940114413/25000000000000 : ℝ)*(f.sum) + (13140434413299/4685000000000000000000000000 : ℝ)*base65 + (1127993639919211981/468500000000000000000000000000000 : ℝ)*base68 + (1984291744891288019/468500000000000000000000000000000 : ℝ)*base69 + (174496223861211981/468500000000000000000000000000000 : ℝ)*base72 + (12598098044959/4685000000000000000000000000 : ℝ)*base73 + (34088150995288019/468500000000000000000000000000000 : ℝ)*base75 + (834204028098788019/468500000000000000000000000000000 : ℝ)*base77 + (993471610161211981/468500000000000000000000000000000 : ℝ)*base80 + (3352105233581/1171250000000000000000000000 : ℝ)*base81 + (1517441/156250000000000000000 : ℝ)*base90 + (1517441/156250000000000000000 : ℝ)*base92 + (1517441/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (388449438048815813380532733/58562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (549459593/50000000000000 : ℝ)*(base19) + (1194624353/100000000000000 : ℝ)*(base23) + (36461137/10000000000000 : ℝ)*(lower1) + (68466223/50000000000000 : ℝ)*(upper3) + (42803927/100000000000000 : ℝ)*(lower4) + (34187317/25000000000000 : ℝ)*(upper5) + (828195078010491/25000000000000 : ℝ)*(major0) + (828195078010491/25000000000000 : ℝ)*(major1) + (828195078010491/25000000000000 : ℝ)*(major2) + (641929113/50000000000000 : ℝ)*(sp2) + (4567762325579301/100000000000000 : ℝ)*(sp4) + (2283880613330057/50000000000000 : ℝ)*(sp5) + (2283879923548361/50000000000000 : ℝ)*(sp6) + (51444951935053/2500000000000 : ℝ)*(sp7) + (51444951935053/2500000000000 : ℝ)*(f.failure) + (4567762325579301/100000000000000 : ℝ)*(f.sum) + (2312490765997/1171250000000000000000000000 : ℝ)*base66 + (7634475303704189089/234250000000000000000000000000000 : ℝ)*base68 + (1902863484536189089/234250000000000000000000000000000 : ℝ)*base70 + (15019282331534060911/234250000000000000000000000000000 : ℝ)*base71 + (3520762642679/2342500000000000000000000000 : ℝ)*base74 + (4498064449785939089/234250000000000000000000000000000 : ℝ)*base76 + (608723217470439089/234250000000000000000000000000000 : ℝ)*base78 + (3510870733427939089/234250000000000000000000000000000 : ℝ)*base80 + (7024146948999/2342500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (51649/7812500000000000000 : ℝ)*base89 + (51649/7812500000000000000 : ℝ)*base91 + (51649/7812500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1482_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10793/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5397/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1482_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1482_s7_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-956633233/5000000000 : ℝ)*x 0 + (2718577843/5000000000 : ℝ)*x 1 + (2607989141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (956633233/5000000000 : ℝ)^4461 ≤ (11689387981331/100000000000000 : ℝ)^3437 := by
    have hnat : (956633233 : ℕ)^4461*100000000000000^3437 ≤ 11689387981331^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      956633233 5000000000 11689387981331 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718577843/5000000000 : ℝ)^4461 ≤ (45345057436843/100000000000000 : ℝ)^3437 := by
    have hnat : (2718577843 : ℕ)^4461*100000000000000^3437 ≤ 45345057436843^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718577843 5000000000 45345057436843 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607989141/5000000000 : ℝ)^4461 ≤ (21482777288419/50000000000000 : ℝ)^3437 := by
    have hnat : (2607989141 : ℕ)^4461*50000000000000^3437 ≤ 21482777288419^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607989141 5000000000 21482777288419 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-956633233/5000000000 : ℝ), (2718577843/5000000000 : ℝ), (2607989141/5000000000 : ℝ)] ![(11689387981331/100000000000000 : ℝ), (45345057436843/100000000000000 : ℝ), (21482777288419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-956633233/5000000000 : ℝ)|^4461 ≤ (11689387981331/100000000000000 : ℝ)^3437
        have hw : |(-956633233/5000000000 : ℝ)|=(956633233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718577843/5000000000 : ℝ)|^4461 ≤ (45345057436843/100000000000000 : ℝ)^3437
        have hw : |(2718577843/5000000000 : ℝ)|=(2718577843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607989141/5000000000 : ℝ)|^4461 ≤ (21482777288419/50000000000000 : ℝ)^3437
        have hw : |(2607989141/5000000000 : ℝ)|=(2607989141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s7_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535320243/1000000000 : ℝ)*x 0 + (-1013306877/5000000000 : ℝ)*x 1 + (2607989141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535320243/1000000000 : ℝ)^4461 ≤ (44438396952571/100000000000000 : ℝ)^3437 := by
    have hnat : (535320243 : ℕ)^4461*100000000000000^3437 ≤ 44438396952571^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535320243 1000000000 44438396952571 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013306877/5000000000 : ℝ)^4461 ≤ (3149012114893/25000000000000 : ℝ)^3437 := by
    have hnat : (1013306877 : ℕ)^4461*25000000000000^3437 ≤ 3149012114893^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013306877 5000000000 3149012114893 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607989141/5000000000 : ℝ)^4461 ≤ (21482777288419/50000000000000 : ℝ)^3437 := by
    have hnat : (2607989141 : ℕ)^4461*50000000000000^3437 ≤ 21482777288419^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607989141 5000000000 21482777288419 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535320243/1000000000 : ℝ), (-1013306877/5000000000 : ℝ), (2607989141/5000000000 : ℝ)] ![(44438396952571/100000000000000 : ℝ), (3149012114893/25000000000000 : ℝ), (21482777288419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535320243/1000000000 : ℝ)|^4461 ≤ (44438396952571/100000000000000 : ℝ)^3437
        have hw : |(535320243/1000000000 : ℝ)|=(535320243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1013306877/5000000000 : ℝ)|^4461 ≤ (3149012114893/25000000000000 : ℝ)^3437
        have hw : |(-1013306877/5000000000 : ℝ)|=(1013306877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607989141/5000000000 : ℝ)|^4461 ≤ (21482777288419/50000000000000 : ℝ)^3437
        have hw : |(2607989141/5000000000 : ℝ)|=(2607989141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s7_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535320243/1000000000 : ℝ)*x 0 + (2607989141/5000000000 : ℝ)*x 1 + (-1013306877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535320243/1000000000 : ℝ)^4461 ≤ (44438396952571/100000000000000 : ℝ)^3437 := by
    have hnat : (535320243 : ℕ)^4461*100000000000000^3437 ≤ 44438396952571^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535320243 1000000000 44438396952571 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607989141/5000000000 : ℝ)^4461 ≤ (21482777288419/50000000000000 : ℝ)^3437 := by
    have hnat : (2607989141 : ℕ)^4461*50000000000000^3437 ≤ 21482777288419^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607989141 5000000000 21482777288419 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013306877/5000000000 : ℝ)^4461 ≤ (3149012114893/25000000000000 : ℝ)^3437 := by
    have hnat : (1013306877 : ℕ)^4461*25000000000000^3437 ≤ 3149012114893^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013306877 5000000000 3149012114893 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535320243/1000000000 : ℝ), (2607989141/5000000000 : ℝ), (-1013306877/5000000000 : ℝ)] ![(44438396952571/100000000000000 : ℝ), (21482777288419/50000000000000 : ℝ), (3149012114893/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535320243/1000000000 : ℝ)|^4461 ≤ (44438396952571/100000000000000 : ℝ)^3437
        have hw : |(535320243/1000000000 : ℝ)|=(535320243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607989141/5000000000 : ℝ)|^4461 ≤ (21482777288419/50000000000000 : ℝ)^3437
        have hw : |(2607989141/5000000000 : ℝ)|=(2607989141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1013306877/5000000000 : ℝ)|^4461 ≤ (3149012114893/25000000000000 : ℝ)^3437
        have hw : |(-1013306877/5000000000 : ℝ)|=(1013306877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s7_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4283951297/10000000000 : ℝ)*x 0 + (126393663/312500000 : ℝ)*x 1 + (2267776013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4283951297/10000000000 : ℝ)^4461 ≤ (16639045357717/50000000000000 : ℝ)^3437 := by
    have hnat : (4283951297 : ℕ)^4461*50000000000000^3437 ≤ 16639045357717^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4283951297 10000000000 16639045357717 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126393663/312500000 : ℝ)^4461 ≤ (3088516753789/10000000000000 : ℝ)^3437 := by
    have hnat : (126393663 : ℕ)^4461*10000000000000^3437 ≤ 3088516753789^3437*312500000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126393663 312500000 3088516753789 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267776013/5000000000 : ℝ)^4461 ≤ (17918370866683/50000000000000 : ℝ)^3437 := by
    have hnat : (2267776013 : ℕ)^4461*50000000000000^3437 ≤ 17918370866683^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267776013 5000000000 17918370866683 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4283951297/10000000000 : ℝ), (126393663/312500000 : ℝ), (2267776013/5000000000 : ℝ)] ![(16639045357717/50000000000000 : ℝ), (3088516753789/10000000000000 : ℝ), (17918370866683/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4283951297/10000000000 : ℝ)|^4461 ≤ (16639045357717/50000000000000 : ℝ)^3437
        have hw : |(4283951297/10000000000 : ℝ)|=(4283951297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126393663/312500000 : ℝ)|^4461 ≤ (3088516753789/10000000000000 : ℝ)^3437
        have hw : |(126393663/312500000 : ℝ)|=(126393663/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2267776013/5000000000 : ℝ)|^4461 ≤ (17918370866683/50000000000000 : ℝ)^3437
        have hw : |(2267776013/5000000000 : ℝ)|=(2267776013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s7_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-478324193/2500000000 : ℝ)*x 0 + (652138753/1250000000 : ℝ)*x 1 + (5436015587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (478324193/2500000000 : ℝ)^4461 ≤ (2922407076541/25000000000000 : ℝ)^3437 := by
    have hnat : (478324193 : ℕ)^4461*25000000000000^3437 ≤ 2922407076541^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      478324193 2500000000 2922407076541 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652138753/1250000000 : ℝ)^4461 ≤ (1074441373781/2500000000000 : ℝ)^3437 := by
    have hnat : (652138753 : ℕ)^4461*2500000000000^3437 ≤ 1074441373781^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652138753 1250000000 1074441373781 2500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436015587/10000000000 : ℝ)^4461 ≤ (2833294795907/6250000000000 : ℝ)^3437 := by
    have hnat : (5436015587 : ℕ)^4461*6250000000000^3437 ≤ 2833294795907^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436015587 10000000000 2833294795907 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-478324193/2500000000 : ℝ), (652138753/1250000000 : ℝ), (5436015587/10000000000 : ℝ)] ![(2922407076541/25000000000000 : ℝ), (1074441373781/2500000000000 : ℝ), (2833294795907/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-478324193/2500000000 : ℝ)|^4461 ≤ (2922407076541/25000000000000 : ℝ)^3437
        have hw : |(-478324193/2500000000 : ℝ)|=(478324193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652138753/1250000000 : ℝ)|^4461 ≤ (1074441373781/2500000000000 : ℝ)^3437
        have hw : |(652138753/1250000000 : ℝ)|=(652138753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436015587/10000000000 : ℝ)|^4461 ≤ (2833294795907/6250000000000 : ℝ)^3437
        have hw : |(5436015587/10000000000 : ℝ)|=(5436015587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_s7_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856803701/2000000000 : ℝ)*x 0 + (4533039561/10000000000 : ℝ)*x 1 + (40471281/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856803701/2000000000 : ℝ)^4461 ≤ (16639384169541/50000000000000 : ℝ)^3437 := by
    have hnat : (856803701 : ℕ)^4461*50000000000000^3437 ≤ 16639384169541^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856803701 2000000000 16639384169541 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4533039561/10000000000 : ℝ)^4461 ≤ (35810977618229/100000000000000 : ℝ)^3437 := by
    have hnat : (4533039561 : ℕ)^4461*100000000000000^3437 ≤ 35810977618229^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533039561 10000000000 35810977618229 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40471281/100000000 : ℝ)^4461 ≤ (15455127019391/50000000000000 : ℝ)^3437 := by
    have hnat : (40471281 : ℕ)^4461*50000000000000^3437 ≤ 15455127019391^3437*100000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40471281 100000000 15455127019391 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856803701/2000000000 : ℝ), (4533039561/10000000000 : ℝ), (40471281/100000000 : ℝ)] ![(16639384169541/50000000000000 : ℝ), (35810977618229/100000000000000 : ℝ), (15455127019391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856803701/2000000000 : ℝ)|^4461 ≤ (16639384169541/50000000000000 : ℝ)^3437
        have hw : |(856803701/2000000000 : ℝ)|=(856803701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4533039561/10000000000 : ℝ)|^4461 ≤ (35810977618229/100000000000000 : ℝ)^3437
        have hw : |(4533039561/10000000000 : ℝ)|=(4533039561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40471281/100000000 : ℝ)|^4461 ≤ (15455127019391/50000000000000 : ℝ)^3437
        have hw : |(40471281/100000000 : ℝ)|=(40471281/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5397/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2159/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3869/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5397/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5397/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5397/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5397/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5397/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5397/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5397/50000 : ℝ) ^ (4459/1024 : ℝ) ≤ (6165955326344719/100000000000000000000 : ℝ) := by
    have hpowers : (5397/50000 : ℝ)^4459 ≤ (6165955326344719/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5397 : ℕ)^4459*100000000000000000000^1024 ≤ 6165955326344719^1024*50000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5397 50000 6165955326344719 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5397/50000 : ℝ)) (X := (6165955326344719/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3869/25000 : ℝ) ^ (4459/1024 : ℝ) ≤ (29605693016727567/100000000000000000000 : ℝ) := by
    have hpowers : (3869/25000 : ℝ)^4459 ≤ (29605693016727567/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3869 : ℕ)^4459*100000000000000000000^1024 ≤ 29605693016727567^1024*25000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3869 25000 29605693016727567 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3869/25000 : ℝ)) (X := (29605693016727567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006165955326344719/50000000000000000000 : ℝ) ≤ (2500070796572849/2500000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50006165955326344719/50000000000000000000 : ℝ)^1024 ≤ (2500070796572849/2500000000000000 : ℝ)^4459 := by
      have hnat : (50006165955326344719 : ℕ)^1024*2500000000000000^4459 ≤ 2500070796572849^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006165955326344719 50000000000000000000 2500070796572849 2500000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070796572849/2500000000000000 : ℝ)) (X := (50006165955326344719/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017885824171536143/50000000000000000000 : ℝ) ≤ (500041068761969/500000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50017885824171536143/50000000000000000000 : ℝ)^1024 ≤ (500041068761969/500000000000000 : ℝ)^4459 := by
      have hnat : (50017885824171536143 : ℕ)^1024*500000000000000^4459 ≤ 500041068761969^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017885824171536143 50000000000000000000 500041068761969 500000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500041068761969/500000000000000 : ℝ)) (X := (50017885824171536143/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029605693016727567/50000000000000000000 : ℝ) ≤ (2500339891046841/2500000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50029605693016727567/50000000000000000000 : ℝ)^1024 ≤ (2500339891046841/2500000000000000 : ℝ)^4459 := by
      have hnat : (50029605693016727567 : ℕ)^1024*2500000000000000^4459 ≤ 2500339891046841^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029605693016727567 50000000000000000000 2500339891046841 2500000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500339891046841/2500000000000000 : ℝ)) (X := (50029605693016727567/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6165955326344719/100000000000000000000 : ℝ) ≤ ((1170242686380180937/1170500000000000000 : ℝ)+2*(33636809249/29262500000000 : ℝ)*(5397/50000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (1170242686380180937/1170500000000000000 : ℝ)+2*(33636809249/29262500000000 : ℝ)*(5397/50000 : ℝ)=(2500070796572849/2500000000000000 : ℝ) by norm_num, show 1+2*(6165955326344719/100000000000000000000 : ℝ)=(50006165955326344719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29605693016727567/100000000000000000000 : ℝ)+(6165955326344719/100000000000000000000 : ℝ) ≤ ((1170242686380180937/1170500000000000000 : ℝ)+(33636809249/29262500000000 : ℝ)*((3869/25000 : ℝ)+(5397/50000 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (1170242686380180937/1170500000000000000 : ℝ)+(33636809249/29262500000000 : ℝ)*((3869/25000 : ℝ)+(5397/50000 : ℝ))=(500041068761969/500000000000000 : ℝ) by norm_num, show 1+(29605693016727567/100000000000000000000 : ℝ)+(6165955326344719/100000000000000000000 : ℝ)=(50017885824171536143/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29605693016727567/100000000000000000000 : ℝ) ≤ ((1170242686380180937/1170500000000000000 : ℝ)+2*(33636809249/29262500000000 : ℝ)*(3869/25000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (1170242686380180937/1170500000000000000 : ℝ)+2*(33636809249/29262500000000 : ℝ)*(3869/25000 : ℝ)=(2500339891046841/2500000000000000 : ℝ) by norm_num, show 1+2*(29605693016727567/100000000000000000000 : ℝ)=(50029605693016727567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1170242686380180937/1170500000000000000 : ℝ)*(X 1 0+X 2 0)+(33636809249/29262500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5397/50000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (1170242686380180937/1170500000000000000 : ℝ)) (alpha := (33636809249/29262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1170242686380180937/1170500000000000000 : ℝ)*(X 0 1+X 2 1)+(33636809249/29262500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5397/50000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (1170242686380180937/1170500000000000000 : ℝ)) (alpha := (33636809249/29262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1170242686380180937/1170500000000000000 : ℝ)*(X 0 2+X 1 2)+(33636809249/29262500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (5397/50000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (1170242686380180937/1170500000000000000 : ℝ)) (alpha := (33636809249/29262500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-956633233/5000000000 : ℝ)*X 0 0+(2718577843/5000000000 : ℝ)*X 0 1+(2607989141/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535320243/1000000000 : ℝ)*X 1 0+(-1013306877/5000000000 : ℝ)*X 1 1+(2607989141/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535320243/1000000000 : ℝ)*X 2 0+(2607989141/5000000000 : ℝ)*X 2 1+(-1013306877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4283951297/10000000000 : ℝ)*X 0 0+(126393663/312500000 : ℝ)*X 0 1+(2267776013/5000000000 : ℝ)*X 0 2+(4283951297/10000000000 : ℝ)*X 1 0+(126393663/312500000 : ℝ)*X 1 1+(2267776013/5000000000 : ℝ)*X 1 2+(4283951297/10000000000 : ℝ)*X 2 0+(126393663/312500000 : ℝ)*X 2 1+(2267776013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-478324193/2500000000 : ℝ)*X 0 0+(652138753/1250000000 : ℝ)*X 0 1+(5436015587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((856803701/2000000000 : ℝ)*X 0 0+(4533039561/10000000000 : ℝ)*X 0 1+(40471281/100000000 : ℝ)*X 0 2+(856803701/2000000000 : ℝ)*X 1 0+(4533039561/10000000000 : ℝ)*X 1 1+(40471281/100000000 : ℝ)*X 1 2+(856803701/2000000000 : ℝ)*X 2 0+(4533039561/10000000000 : ℝ)*X 2 1+(40471281/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_s7_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50211814961443410437421381/14631250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (613422089/100000000000000 : ℝ)*(base19) + (143047647/25000000000000 : ℝ)*(base23) + (11036029/50000000000000 : ℝ)*(lower2) + (17190787/20000000000000 : ℝ)*(upper3) + (55549773/100000000000000 : ℝ)*(upper5) + (1639533236364879/50000000000000 : ℝ)*(major0) + (1639533236364879/50000000000000 : ℝ)*(major1) + (1639533236364879/50000000000000 : ℝ)*(major2) + (282579208227307/6250000000000 : ℝ)*(sp0) + (2260638074410661/50000000000000 : ℝ)*(sp1) + (565159523756603/12500000000000 : ℝ)*(sp2) + (203685145739541/10000000000000 : ℝ)*(sp3) + (9430606499/100000000000000 : ℝ)*(sp4) + (461142669/10000000000000 : ℝ)*(sp5) + (20368560688221/1000000000000 : ℝ)*(f.failure) + (4521276762243411/100000000000000 : ℝ)*(f.sum) + (6209894137367/1463125000000000000000000000 : ℝ)*base65 + (297146043482501623/58525000000000000000000000000000 : ℝ)*base67 + (653361645653526623/58525000000000000000000000000000 : ℝ)*base69 + (46399710915048377/58525000000000000000000000000000 : ℝ)*base72 + (24260952387113/5852500000000000000000000000 : ℝ)*base73 + (213166811701351623/58525000000000000000000000000000 : ℝ)*base75 + (146794248528451623/58525000000000000000000000000000 : ℝ)*base77 + (161599758003501623/58525000000000000000000000000000 : ℝ)*base79 + (19949856588329/2926250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (19407/3125000000000000000 : ℝ)*base90 + (19407/3125000000000000000 : ℝ)*base92 + (19407/3125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1482_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5397/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2159/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1482_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1482_box_0 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1694110881/10000000000 : ℝ)*x 0 + (108121673/200000000 : ℝ)*x 1 + (1351520989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1694110881/10000000000 : ℝ)^4461 ≤ (9981991568861/100000000000000 : ℝ)^3437 := by
    have hnat : (1694110881 : ℕ)^4461*100000000000000^3437 ≤ 9981991568861^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694110881 10000000000 9981991568861 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108121673/200000000 : ℝ)^4461 ≤ (45009002548711/100000000000000 : ℝ)^3437 := by
    have hnat : (108121673 : ℕ)^4461*100000000000000^3437 ≤ 45009002548711^3437*200000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108121673 200000000 45009002548711 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351520989/2500000000 : ℝ)^4461 ≤ (2250450292769/5000000000000 : ℝ)^3437 := by
    have hnat : (1351520989 : ℕ)^4461*5000000000000^3437 ≤ 2250450292769^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351520989 2500000000 2250450292769 5000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1694110881/10000000000 : ℝ), (108121673/200000000 : ℝ), (1351520989/2500000000 : ℝ)] ![(9981991568861/100000000000000 : ℝ), (45009002548711/100000000000000 : ℝ), (2250450292769/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1694110881/10000000000 : ℝ)|^4461 ≤ (9981991568861/100000000000000 : ℝ)^3437
        have hw : |(-1694110881/10000000000 : ℝ)|=(1694110881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108121673/200000000 : ℝ)|^4461 ≤ (45009002548711/100000000000000 : ℝ)^3437
        have hw : |(108121673/200000000 : ℝ)|=(108121673/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351520989/2500000000 : ℝ)|^4461 ≤ (2250450292769/5000000000000 : ℝ)^3437
        have hw : |(1351520989/2500000000 : ℝ)|=(1351520989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_1 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635137679/5000000000 : ℝ)*x 0 + (-470562569/2500000000 : ℝ)*x 1 + (5406083759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635137679/5000000000 : ℝ)^4461 ≤ (43546968053583/100000000000000 : ℝ)^3437 := by
    have hnat : (2635137679 : ℕ)^4461*100000000000000^3437 ≤ 43546968053583^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635137679 5000000000 43546968053583 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (470562569/2500000000 : ℝ)^4461 ≤ (5722014098663/50000000000000 : ℝ)^3437 := by
    have hnat : (470562569 : ℕ)^4461*50000000000000^3437 ≤ 5722014098663^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470562569 2500000000 5722014098663 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406083759/10000000000 : ℝ)^4461 ≤ (45009003726577/100000000000000 : ℝ)^3437 := by
    have hnat : (5406083759 : ℕ)^4461*100000000000000^3437 ≤ 45009003726577^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406083759 10000000000 45009003726577 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635137679/5000000000 : ℝ), (-470562569/2500000000 : ℝ), (5406083759/10000000000 : ℝ)] ![(43546968053583/100000000000000 : ℝ), (5722014098663/50000000000000 : ℝ), (45009003726577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635137679/5000000000 : ℝ)|^4461 ≤ (43546968053583/100000000000000 : ℝ)^3437
        have hw : |(2635137679/5000000000 : ℝ)|=(2635137679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-470562569/2500000000 : ℝ)|^4461 ≤ (5722014098663/50000000000000 : ℝ)^3437
        have hw : |(-470562569/2500000000 : ℝ)|=(470562569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406083759/10000000000 : ℝ)|^4461 ≤ (45009003726577/100000000000000 : ℝ)^3437
        have hw : |(5406083759/10000000000 : ℝ)|=(5406083759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_2 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270275567/10000000000 : ℝ)*x 0 + (1351520907/2500000000 : ℝ)*x 1 + (-1882250173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270275567/10000000000 : ℝ)^4461 ≤ (8709394059001/20000000000000 : ℝ)^3437 := by
    have hnat : (5270275567 : ℕ)^4461*20000000000000^3437 ≤ 8709394059001^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270275567 10000000000 8709394059001 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351520907/2500000000 : ℝ)^4461 ≤ (703265661109/1562500000000 : ℝ)^3437 := by
    have hnat : (1351520907 : ℕ)^4461*1562500000000^3437 ≤ 703265661109^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351520907 2500000000 703265661109 1562500000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882250173/10000000000 : ℝ)^4461 ≤ (11444027384511/100000000000000 : ℝ)^3437 := by
    have hnat : (1882250173 : ℕ)^4461*100000000000000^3437 ≤ 11444027384511^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882250173 10000000000 11444027384511 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270275567/10000000000 : ℝ), (1351520907/2500000000 : ℝ), (-1882250173/10000000000 : ℝ)] ![(8709394059001/20000000000000 : ℝ), (703265661109/1562500000000 : ℝ), (11444027384511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270275567/10000000000 : ℝ)|^4461 ≤ (8709394059001/20000000000000 : ℝ)^3437
        have hw : |(5270275567/10000000000 : ℝ)|=(5270275567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351520907/2500000000 : ℝ)|^4461 ≤ (703265661109/1562500000000 : ℝ)^3437
        have hw : |(1351520907/2500000000 : ℝ)|=(1351520907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1882250173/10000000000 : ℝ)|^4461 ≤ (11444027384511/100000000000000 : ℝ)^3437
        have hw : |(-1882250173/10000000000 : ℝ)|=(1882250173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_3 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4488451277/10000000000 : ℝ)*x 0 + (4188884697/10000000000 : ℝ)*x 1 + (4188885021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4488451277/10000000000 : ℝ)^4461 ≤ (35354455511019/100000000000000 : ℝ)^3437 := by
    have hnat : (4488451277 : ℕ)^4461*100000000000000^3437 ≤ 35354455511019^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488451277 10000000000 35354455511019 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4188884697/10000000000 : ℝ)^4461 ≤ (32322770611291/100000000000000 : ℝ)^3437 := by
    have hnat : (4188884697 : ℕ)^4461*100000000000000^3437 ≤ 32322770611291^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188884697 10000000000 32322770611291 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4188885021/10000000000 : ℝ)^4461 ≤ (32322773856241/100000000000000 : ℝ)^3437 := by
    have hnat : (4188885021 : ℕ)^4461*100000000000000^3437 ≤ 32322773856241^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4188885021 10000000000 32322773856241 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4488451277/10000000000 : ℝ), (4188884697/10000000000 : ℝ), (4188885021/10000000000 : ℝ)] ![(35354455511019/100000000000000 : ℝ), (32322770611291/100000000000000 : ℝ), (32322773856241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4488451277/10000000000 : ℝ)|^4461 ≤ (35354455511019/100000000000000 : ℝ)^3437
        have hw : |(4488451277/10000000000 : ℝ)|=(4488451277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4188884697/10000000000 : ℝ)|^4461 ≤ (32322770611291/100000000000000 : ℝ)^3437
        have hw : |(4188884697/10000000000 : ℝ)|=(4188884697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4188885021/10000000000 : ℝ)|^4461 ≤ (32322773856241/100000000000000 : ℝ)^3437
        have hw : |(4188885021/10000000000 : ℝ)|=(4188885021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_4 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137881369/10000000000 : ℝ)*x 0 + (5242520437/10000000000 : ℝ)*x 1 + (2621260699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137881369/10000000000 : ℝ)^4461 ≤ (843806352107/6250000000000 : ℝ)^3437 := by
    have hnat : (2137881369 : ℕ)^4461*6250000000000^3437 ≤ 843806352107^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137881369 10000000000 843806352107 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242520437/10000000000 : ℝ)^4461 ≤ (21624772016321/50000000000000 : ℝ)^3437 := by
    have hnat : (5242520437 : ℕ)^4461*50000000000000^3437 ≤ 21624772016321^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242520437 10000000000 21624772016321 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621260699/5000000000 : ℝ)^4461 ≤ (10812388580673/25000000000000 : ℝ)^3437 := by
    have hnat : (2621260699 : ℕ)^4461*25000000000000^3437 ≤ 10812388580673^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621260699 5000000000 10812388580673 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137881369/10000000000 : ℝ), (5242520437/10000000000 : ℝ), (2621260699/5000000000 : ℝ)] ![(843806352107/6250000000000 : ℝ), (21624772016321/50000000000000 : ℝ), (10812388580673/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137881369/10000000000 : ℝ)|^4461 ≤ (843806352107/6250000000000 : ℝ)^3437
        have hw : |(-2137881369/10000000000 : ℝ)|=(2137881369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242520437/10000000000 : ℝ)|^4461 ≤ (21624772016321/50000000000000 : ℝ)^3437
        have hw : |(5242520437/10000000000 : ℝ)|=(5242520437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621260699/5000000000 : ℝ)|^4461 ≤ (10812388580673/25000000000000 : ℝ)^3437
        have hw : |(2621260699/5000000000 : ℝ)|=(2621260699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_5 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692209231/5000000000 : ℝ)*x 0 + (-1949236121/10000000000 : ℝ)*x 1 + (1048504273/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692209231/5000000000 : ℝ)^4461 ≤ (22387513038453/50000000000000 : ℝ)^3437 := by
    have hnat : (2692209231 : ℕ)^4461*50000000000000^3437 ≤ 22387513038453^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692209231 5000000000 22387513038453 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1949236121/10000000000 : ℝ)^4461 ≤ (5987709972887/50000000000000 : ℝ)^3437 := by
    have hnat : (1949236121 : ℕ)^4461*50000000000000^3437 ≤ 5987709972887^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949236121 10000000000 5987709972887 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048504273/2000000000 : ℝ)^4461 ≤ (2162477698467/5000000000000 : ℝ)^3437 := by
    have hnat : (1048504273 : ℕ)^4461*5000000000000^3437 ≤ 2162477698467^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048504273 2000000000 2162477698467 5000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692209231/5000000000 : ℝ), (-1949236121/10000000000 : ℝ), (1048504273/2000000000 : ℝ)] ![(22387513038453/50000000000000 : ℝ), (5987709972887/50000000000000 : ℝ), (2162477698467/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692209231/5000000000 : ℝ)|^4461 ≤ (22387513038453/50000000000000 : ℝ)^3437
        have hw : |(2692209231/5000000000 : ℝ)|=(2692209231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1949236121/10000000000 : ℝ)|^4461 ≤ (5987709972887/50000000000000 : ℝ)^3437
        have hw : |(-1949236121/10000000000 : ℝ)|=(1949236121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048504273/2000000000 : ℝ)|^4461 ≤ (2162477698467/5000000000000 : ℝ)^3437
        have hw : |(1048504273/2000000000 : ℝ)|=(1048504273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_6 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538441867/1000000000 : ℝ)*x 0 + (655315109/1250000000 : ℝ)*x 1 + (-3898473/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538441867/1000000000 : ℝ)^4461 ≤ (4477502832189/10000000000000 : ℝ)^3437 := by
    have hnat : (538441867 : ℕ)^4461*10000000000000^3437 ≤ 4477502832189^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538441867 1000000000 4477502832189 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655315109/1250000000 : ℝ)^4461 ≤ (43249548690469/100000000000000 : ℝ)^3437 := by
    have hnat : (655315109 : ℕ)^4461*100000000000000^3437 ≤ 43249548690469^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655315109 1250000000 43249548690469 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3898473/20000000 : ℝ)^4461 ≤ (598771148397/5000000000000 : ℝ)^3437 := by
    have hnat : (3898473 : ℕ)^4461*5000000000000^3437 ≤ 598771148397^3437*20000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3898473 20000000 598771148397 5000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538441867/1000000000 : ℝ), (655315109/1250000000 : ℝ), (-3898473/20000000 : ℝ)] ![(4477502832189/10000000000000 : ℝ), (43249548690469/100000000000000 : ℝ), (598771148397/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538441867/1000000000 : ℝ)|^4461 ≤ (4477502832189/10000000000000 : ℝ)^3437
        have hw : |(538441867/1000000000 : ℝ)|=(538441867/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655315109/1250000000 : ℝ)|^4461 ≤ (43249548690469/100000000000000 : ℝ)^3437
        have hw : |(655315109/1250000000 : ℝ)|=(655315109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3898473/20000000 : ℝ)|^4461 ≤ (598771148397/5000000000000 : ℝ)^3437
        have hw : |(-3898473/20000000 : ℝ)|=(3898473/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_7 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (509647687/1250000000 : ℝ)*x 0 + (4394381283/10000000000 : ℝ)*x 1 + (439438147/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (509647687/1250000000 : ℝ)^4461 ≤ (7802126136663/25000000000000 : ℝ)^3437 := by
    have hnat : (509647687 : ℕ)^4461*25000000000000^3437 ≤ 7802126136663^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509647687 1250000000 7802126136663 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4394381283/10000000000 : ℝ)^4461 ≤ (34395746768549/100000000000000 : ℝ)^3437 := by
    have hnat : (4394381283 : ℕ)^4461*100000000000000^3437 ≤ 34395746768549^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394381283 10000000000 34395746768549 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439438147/1000000000 : ℝ)^4461 ≤ (214973429177/625000000000 : ℝ)^3437 := by
    have hnat : (439438147 : ℕ)^4461*625000000000^3437 ≤ 214973429177^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439438147 1000000000 214973429177 625000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(509647687/1250000000 : ℝ), (4394381283/10000000000 : ℝ), (439438147/1000000000 : ℝ)] ![(7802126136663/25000000000000 : ℝ), (34395746768549/100000000000000 : ℝ), (214973429177/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(509647687/1250000000 : ℝ)|^4461 ≤ (7802126136663/25000000000000 : ℝ)^3437
        have hw : |(509647687/1250000000 : ℝ)|=(509647687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4394381283/10000000000 : ℝ)|^4461 ≤ (34395746768549/100000000000000 : ℝ)^3437
        have hw : |(4394381283/10000000000 : ℝ)|=(4394381283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(439438147/1000000000 : ℝ)|^4461 ≤ (214973429177/625000000000 : ℝ)^3437
        have hw : |(439438147/1000000000 : ℝ)|=(439438147/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_8 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1022136827/5000000000 : ℝ)*x 0 + (5128273171/10000000000 : ℝ)*x 1 + (678327973/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1022136827/5000000000 : ℝ)^4461 ≤ (509547869271/4000000000000 : ℝ)^3437 := by
    have hnat : (1022136827 : ℕ)^4461*4000000000000^3437 ≤ 509547869271^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1022136827 5000000000 509547869271 4000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5128273171/10000000000 : ℝ)^4461 ≤ (42030216279623/100000000000000 : ℝ)^3437 := by
    have hnat : (5128273171 : ℕ)^4461*100000000000000^3437 ≤ 42030216279623^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5128273171 10000000000 42030216279623 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678327973/1250000000 : ℝ)^4461 ≤ (45231086978137/100000000000000 : ℝ)^3437 := by
    have hnat : (678327973 : ℕ)^4461*100000000000000^3437 ≤ 45231086978137^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678327973 1250000000 45231086978137 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1022136827/5000000000 : ℝ), (5128273171/10000000000 : ℝ), (678327973/1250000000 : ℝ)] ![(509547869271/4000000000000 : ℝ), (42030216279623/100000000000000 : ℝ), (45231086978137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1022136827/5000000000 : ℝ)|^4461 ≤ (509547869271/4000000000000 : ℝ)^3437
        have hw : |(-1022136827/5000000000 : ℝ)|=(1022136827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5128273171/10000000000 : ℝ)|^4461 ≤ (42030216279623/100000000000000 : ℝ)^3437
        have hw : |(5128273171/10000000000 : ℝ)|=(5128273171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678327973/1250000000 : ℝ)|^4461 ≤ (45231086978137/100000000000000 : ℝ)^3437
        have hw : |(678327973/1250000000 : ℝ)|=(678327973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_9 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131398361/250000000 : ℝ)*x 0 + (-1873583727/10000000000 : ℝ)*x 1 + (5426623591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131398361/250000000 : ℝ)^4461 ≤ (8678646234293/20000000000000 : ℝ)^3437 := by
    have hnat : (131398361 : ℕ)^4461*20000000000000^3437 ≤ 8678646234293^3437*250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131398361 250000000 8678646234293 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1873583727/10000000000 : ℝ)^4461 ≤ (1421960490463/12500000000000 : ℝ)^3437 := by
    have hnat : (1873583727 : ℕ)^4461*12500000000000^3437 ≤ 1421960490463^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873583727 10000000000 1421960490463 12500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426623591/10000000000 : ℝ)^4461 ≤ (226155424451/500000000000 : ℝ)^3437 := by
    have hnat : (5426623591 : ℕ)^4461*500000000000^3437 ≤ 226155424451^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426623591 10000000000 226155424451 500000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131398361/250000000 : ℝ), (-1873583727/10000000000 : ℝ), (5426623591/10000000000 : ℝ)] ![(8678646234293/20000000000000 : ℝ), (1421960490463/12500000000000 : ℝ), (226155424451/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131398361/250000000 : ℝ)|^4461 ≤ (8678646234293/20000000000000 : ℝ)^3437
        have hw : |(131398361/250000000 : ℝ)|=(131398361/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1873583727/10000000000 : ℝ)|^4461 ≤ (1421960490463/12500000000000 : ℝ)^3437
        have hw : |(-1873583727/10000000000 : ℝ)|=(1873583727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426623591/10000000000 : ℝ)|^4461 ≤ (226155424451/500000000000 : ℝ)^3437
        have hw : |(5426623591/10000000000 : ℝ)|=(5426623591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_10 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210237369/400000000 : ℝ)*x 0 + (169581973/312500000 : ℝ)*x 1 + (-468396161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210237369/400000000 : ℝ)^4461 ≤ (2712076804223/6250000000000 : ℝ)^3437 := by
    have hnat : (210237369 : ℕ)^4461*6250000000000^3437 ≤ 2712076804223^3437*400000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210237369 400000000 2712076804223 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169581973/312500000 : ℝ)^4461 ≤ (45231079967863/100000000000000 : ℝ)^3437 := by
    have hnat : (169581973 : ℕ)^4461*100000000000000^3437 ≤ 45231079967863^3437*312500000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169581973 312500000 45231079967863 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (468396161/2500000000 : ℝ)^4461 ≤ (5687845575089/50000000000000 : ℝ)^3437 := by
    have hnat : (468396161 : ℕ)^4461*50000000000000^3437 ≤ 5687845575089^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468396161 2500000000 5687845575089 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210237369/400000000 : ℝ), (169581973/312500000 : ℝ), (-468396161/2500000000 : ℝ)] ![(2712076804223/6250000000000 : ℝ), (45231079967863/100000000000000 : ℝ), (5687845575089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210237369/400000000 : ℝ)|^4461 ≤ (2712076804223/6250000000000 : ℝ)^3437
        have hw : |(210237369/400000000 : ℝ)|=(210237369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169581973/312500000 : ℝ)|^4461 ≤ (45231079967863/100000000000000 : ℝ)^3437
        have hw : |(169581973/312500000 : ℝ)|=(169581973/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-468396161/2500000000 : ℝ)|^4461 ≤ (5687845575089/50000000000000 : ℝ)^3437
        have hw : |(-468396161/2500000000 : ℝ)|=(468396161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_11 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2269471063/5000000000 : ℝ)*x 0 + (1040761853/2500000000 : ℝ)*x 1 + (4163047937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2269471063/5000000000 : ℝ)^4461 ≤ (35871512311327/100000000000000 : ℝ)^3437 := by
    have hnat : (2269471063 : ℕ)^4461*100000000000000^3437 ≤ 35871512311327^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269471063 5000000000 35871512311327 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040761853/2500000000 : ℝ)^4461 ≤ (8016060303593/25000000000000 : ℝ)^3437 := by
    have hnat : (1040761853 : ℕ)^4461*25000000000000^3437 ≤ 8016060303593^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040761853 2500000000 8016060303593 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163047937/10000000000 : ℝ)^4461 ≤ (8016061615677/25000000000000 : ℝ)^3437 := by
    have hnat : (4163047937 : ℕ)^4461*25000000000000^3437 ≤ 8016061615677^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163047937 10000000000 8016061615677 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2269471063/5000000000 : ℝ), (1040761853/2500000000 : ℝ), (4163047937/10000000000 : ℝ)] ![(35871512311327/100000000000000 : ℝ), (8016060303593/25000000000000 : ℝ), (8016061615677/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2269471063/5000000000 : ℝ)|^4461 ≤ (35871512311327/100000000000000 : ℝ)^3437
        have hw : |(2269471063/5000000000 : ℝ)|=(2269471063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040761853/2500000000 : ℝ)|^4461 ≤ (8016060303593/25000000000000 : ℝ)^3437
        have hw : |(1040761853/2500000000 : ℝ)|=(1040761853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163047937/10000000000 : ℝ)|^4461 ≤ (8016061615677/25000000000000 : ℝ)^3437
        have hw : |(4163047937/10000000000 : ℝ)|=(4163047937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_12 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1787838153/10000000000 : ℝ)*x 0 + (5516550151/10000000000 : ℝ)*x 1 + (1045505067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1787838153/10000000000 : ℝ)^4461 ≤ (2140923571473/20000000000000 : ℝ)^3437 := by
    have hnat : (1787838153 : ℕ)^4461*20000000000000^3437 ≤ 2140923571473^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787838153 10000000000 2140923571473 20000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5516550151/10000000000 : ℝ)^4461 ≤ (11551582977903/25000000000000 : ℝ)^3437 := by
    have hnat : (5516550151 : ℕ)^4461*25000000000000^3437 ≤ 11551582977903^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516550151 10000000000 11551582977903 25000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1045505067/2000000000 : ℝ)^4461 ≤ (43089050215967/100000000000000 : ℝ)^3437 := by
    have hnat : (1045505067 : ℕ)^4461*100000000000000^3437 ≤ 43089050215967^3437*2000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045505067 2000000000 43089050215967 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1787838153/10000000000 : ℝ), (5516550151/10000000000 : ℝ), (1045505067/2000000000 : ℝ)] ![(2140923571473/20000000000000 : ℝ), (11551582977903/25000000000000 : ℝ), (43089050215967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1787838153/10000000000 : ℝ)|^4461 ≤ (2140923571473/20000000000000 : ℝ)^3437
        have hw : |(-1787838153/10000000000 : ℝ)|=(1787838153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5516550151/10000000000 : ℝ)|^4461 ≤ (11551582977903/25000000000000 : ℝ)^3437
        have hw : |(5516550151/10000000000 : ℝ)|=(5516550151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1045505067/2000000000 : ℝ)|^4461 ≤ (43089050215967/100000000000000 : ℝ)^3437
        have hw : |(1045505067/2000000000 : ℝ)|=(1045505067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_13 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (674360277/1250000000 : ℝ)*x 0 + (-1955194149/10000000000 : ℝ)*x 1 + (2613762787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674360277/1250000000 : ℝ)^4461 ≤ (22443998009357/50000000000000 : ℝ)^3437 := by
    have hnat : (674360277 : ℕ)^4461*50000000000000^3437 ≤ 22443998009357^3437*1250000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674360277 1250000000 22443998009357 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1955194149/10000000000 : ℝ)^4461 ≤ (6011475590151/50000000000000 : ℝ)^3437 := by
    have hnat : (1955194149 : ℕ)^4461*50000000000000^3437 ≤ 6011475590151^3437*10000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1955194149 10000000000 6011475590151 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613762787/5000000000 : ℝ)^4461 ≤ (2693065798307/6250000000000 : ℝ)^3437 := by
    have hnat : (2613762787 : ℕ)^4461*6250000000000^3437 ≤ 2693065798307^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613762787 5000000000 2693065798307 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(674360277/1250000000 : ℝ), (-1955194149/10000000000 : ℝ), (2613762787/5000000000 : ℝ)] ![(22443998009357/50000000000000 : ℝ), (6011475590151/50000000000000 : ℝ), (2693065798307/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(674360277/1250000000 : ℝ)|^4461 ≤ (22443998009357/50000000000000 : ℝ)^3437
        have hw : |(674360277/1250000000 : ℝ)|=(674360277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1955194149/10000000000 : ℝ)|^4461 ≤ (6011475590151/50000000000000 : ℝ)^3437
        have hw : |(-1955194149/10000000000 : ℝ)|=(1955194149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613762787/5000000000 : ℝ)|^4461 ≤ (2693065798307/6250000000000 : ℝ)^3437
        have hw : |(2613762787/5000000000 : ℝ)|=(2613762787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_14 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697441117/5000000000 : ℝ)*x 0 + (2613762713/5000000000 : ℝ)*x 1 + (-488798581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697441117/5000000000 : ℝ)^4461 ≤ (2805499763319/6250000000000 : ℝ)^3437 := by
    have hnat : (2697441117 : ℕ)^4461*6250000000000^3437 ≤ 2805499763319^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697441117 5000000000 2805499763319 6250000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613762713/5000000000 : ℝ)^4461 ≤ (43089051189531/100000000000000 : ℝ)^3437 := by
    have hnat : (2613762713 : ℕ)^4461*100000000000000^3437 ≤ 43089051189531^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613762713 5000000000 43089051189531 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488798581/2500000000 : ℝ)^4461 ≤ (1202295257703/10000000000000 : ℝ)^3437 := by
    have hnat : (488798581 : ℕ)^4461*10000000000000^3437 ≤ 1202295257703^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488798581 2500000000 1202295257703 10000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697441117/5000000000 : ℝ), (2613762713/5000000000 : ℝ), (-488798581/2500000000 : ℝ)] ![(2805499763319/6250000000000 : ℝ), (43089051189531/100000000000000 : ℝ), (1202295257703/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697441117/5000000000 : ℝ)|^4461 ≤ (2805499763319/6250000000000 : ℝ)^3437
        have hw : |(2697441117/5000000000 : ℝ)|=(2697441117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613762713/5000000000 : ℝ)|^4461 ≤ (43089051189531/100000000000000 : ℝ)^3437
        have hw : |(2613762713/5000000000 : ℝ)|=(2613762713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488798581/2500000000 : ℝ)|^4461 ≤ (1202295257703/10000000000000 : ℝ)^3437
        have hw : |(-488798581/2500000000 : ℝ)|=(488798581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1482_box_15 (p : ℝ) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2019308589/5000000000 : ℝ)*x 0 + (441319931/1000000000 : ℝ)*x 1 + (1103299811/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2019308589/5000000000 : ℝ)^4461 ≤ (15412955544607/50000000000000 : ℝ)^3437 := by
    have hnat : (2019308589 : ℕ)^4461*50000000000000^3437 ≤ 15412955544607^3437*5000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019308589 5000000000 15412955544607 50000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441319931/1000000000 : ℝ)^4461 ≤ (34587044784293/100000000000000 : ℝ)^3437 := by
    have hnat : (441319931 : ℕ)^4461*100000000000000^3437 ≤ 34587044784293^3437*1000000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441319931 1000000000 34587044784293 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103299811/2500000000 : ℝ)^4461 ≤ (34587044112931/100000000000000 : ℝ)^3437 := by
    have hnat : (1103299811 : ℕ)^4461*100000000000000^3437 ≤ 34587044112931^3437*2500000000^4461 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103299811 2500000000 34587044112931 100000000000000 4461 3437 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4461/1024 : ℝ)) 4461 3437 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2019308589/5000000000 : ℝ), (441319931/1000000000 : ℝ), (1103299811/2500000000 : ℝ)] ![(15412955544607/50000000000000 : ℝ), (34587044784293/100000000000000 : ℝ), (34587044112931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2019308589/5000000000 : ℝ)|^4461 ≤ (15412955544607/50000000000000 : ℝ)^3437
        have hw : |(2019308589/5000000000 : ℝ)|=(2019308589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(441319931/1000000000 : ℝ)|^4461 ≤ (34587044784293/100000000000000 : ℝ)^3437
        have hw : |(441319931/1000000000 : ℝ)|=(441319931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103299811/2500000000 : ℝ)|^4461 ≤ (34587044112931/100000000000000 : ℝ)^3437
        have hw : |(1103299811/2500000000 : ℝ)|=(1103299811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1482_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2159/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7963/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58487/100000 : ℝ) ∧ (7999/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85807/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2159/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2159/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2159/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2159/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2159/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2159/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2159/20000 : ℝ) ^ (4459/1024 : ℝ) ≤ (6168443169283103/100000000000000000000 : ℝ) := by
    have hpowers : (2159/20000 : ℝ)^4459 ≤ (6168443169283103/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2159 : ℕ)^4459*100000000000000000000^1024 ≤ 6168443169283103^1024*20000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2159 20000 6168443169283103 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2159/20000 : ℝ)) (X := (6168443169283103/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3869/25000 : ℝ) ^ (4459/1024 : ℝ) ≤ (29605693016727567/100000000000000000000 : ℝ) := by
    have hpowers : (3869/25000 : ℝ)^4459 ≤ (29605693016727567/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3869 : ℕ)^4459*100000000000000000000^1024 ≤ 29605693016727567^1024*25000^4459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3869 25000 29605693016727567 100000000000000000000 4459 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3869/25000 : ℝ)) (X := (29605693016727567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006168443169283103/50000000000000000000 : ℝ) ≤ (10000283300546123/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50006168443169283103/50000000000000000000 : ℝ)^1024 ≤ (10000283300546123/10000000000000000 : ℝ)^4459 := by
      have hnat : (50006168443169283103 : ℕ)^1024*10000000000000000^4459 ≤ 10000283300546123^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006168443169283103 50000000000000000000 10000283300546123 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000283300546123/10000000000000000 : ℝ)) (X := (50006168443169283103/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003577413618601067/10000000000000000000 : ℝ) ≤ (625051339522277/625000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (10003577413618601067/10000000000000000000 : ℝ)^1024 ≤ (625051339522277/625000000000000 : ℝ)^4459 := by
      have hnat : (10003577413618601067 : ℕ)^1024*625000000000000^4459 ≤ 625051339522277^4459*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003577413618601067 10000000000000000000 625051339522277 625000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625051339522277/625000000000000 : ℝ)) (X := (10003577413618601067/10000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029605693016727567/50000000000000000000 : ℝ) ≤ (10001359564166741/10000000000000000 : ℝ) ^ (4459/1024 : ℝ) := by
    have hpowers : (50029605693016727567/50000000000000000000 : ℝ)^1024 ≤ (10001359564166741/10000000000000000 : ℝ)^4459 := by
      have hnat : (50029605693016727567 : ℕ)^1024*10000000000000000^4459 ≤ 10001359564166741^4459*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029605693016727567 50000000000000000000 10001359564166741 10000000000000000 1024 4459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001359564166741/10000000000000000 : ℝ)) (X := (50029605693016727567/50000000000000000000 : ℝ)) (by norm_num) 4459 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6168443169283103/100000000000000000000 : ℝ) ≤ ((46799707864071830453/46810000000000000000 : ℝ)+2*(538131810309/468100000000000 : ℝ)*(2159/20000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (46799707864071830453/46810000000000000000 : ℝ)+2*(538131810309/468100000000000 : ℝ)*(2159/20000 : ℝ)=(10000283300546123/10000000000000000 : ℝ) by norm_num, show 1+2*(6168443169283103/100000000000000000000 : ℝ)=(50006168443169283103/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29605693016727567/100000000000000000000 : ℝ)+(6168443169283103/100000000000000000000 : ℝ) ≤ ((46799707864071830453/46810000000000000000 : ℝ)+(538131810309/468100000000000 : ℝ)*((3869/25000 : ℝ)+(2159/20000 : ℝ)))^(4459/1024 : ℝ) := by
    rw [show (46799707864071830453/46810000000000000000 : ℝ)+(538131810309/468100000000000 : ℝ)*((3869/25000 : ℝ)+(2159/20000 : ℝ))=(625051339522277/625000000000000 : ℝ) by norm_num, show 1+(29605693016727567/100000000000000000000 : ℝ)+(6168443169283103/100000000000000000000 : ℝ)=(10003577413618601067/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29605693016727567/100000000000000000000 : ℝ) ≤ ((46799707864071830453/46810000000000000000 : ℝ)+2*(538131810309/468100000000000 : ℝ)*(3869/25000 : ℝ))^(4459/1024 : ℝ) := by
    rw [show (46799707864071830453/46810000000000000000 : ℝ)+2*(538131810309/468100000000000 : ℝ)*(3869/25000 : ℝ)=(10001359564166741/10000000000000000 : ℝ) by norm_num, show 1+2*(29605693016727567/100000000000000000000 : ℝ)=(50029605693016727567/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46799707864071830453/46810000000000000000 : ℝ)*(X 1 0+X 2 0)+(538131810309/468100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (2159/20000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (46799707864071830453/46810000000000000000 : ℝ)) (alpha := (538131810309/468100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46799707864071830453/46810000000000000000 : ℝ)*(X 0 1+X 2 1)+(538131810309/468100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (2159/20000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (46799707864071830453/46810000000000000000 : ℝ)) (alpha := (538131810309/468100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46799707864071830453/46810000000000000000 : ℝ)*(X 0 2+X 1 2)+(538131810309/468100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4459/1024 : ℝ)) (lo := (2159/20000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (46799707864071830453/46810000000000000000 : ℝ)) (alpha := (538131810309/468100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1694110881/10000000000 : ℝ)*X 0 0+(108121673/200000000 : ℝ)*X 0 1+(1351520989/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635137679/5000000000 : ℝ)*X 1 0+(-470562569/2500000000 : ℝ)*X 1 1+(5406083759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270275567/10000000000 : ℝ)*X 2 0+(1351520907/2500000000 : ℝ)*X 2 1+(-1882250173/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4488451277/10000000000 : ℝ)*X 0 0+(4188884697/10000000000 : ℝ)*X 0 1+(4188885021/10000000000 : ℝ)*X 0 2+(4488451277/10000000000 : ℝ)*X 1 0+(4188884697/10000000000 : ℝ)*X 1 1+(4188885021/10000000000 : ℝ)*X 1 2+(4488451277/10000000000 : ℝ)*X 2 0+(4188884697/10000000000 : ℝ)*X 2 1+(4188885021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2137881369/10000000000 : ℝ)*X 0 0+(5242520437/10000000000 : ℝ)*X 0 1+(2621260699/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692209231/5000000000 : ℝ)*X 1 0+(-1949236121/10000000000 : ℝ)*X 1 1+(1048504273/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((538441867/1000000000 : ℝ)*X 2 0+(655315109/1250000000 : ℝ)*X 2 1+(-3898473/20000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((509647687/1250000000 : ℝ)*X 0 0+(4394381283/10000000000 : ℝ)*X 0 1+(439438147/1000000000 : ℝ)*X 0 2+(509647687/1250000000 : ℝ)*X 1 0+(4394381283/10000000000 : ℝ)*X 1 1+(439438147/1000000000 : ℝ)*X 1 2+(509647687/1250000000 : ℝ)*X 2 0+(4394381283/10000000000 : ℝ)*X 2 1+(439438147/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1022136827/5000000000 : ℝ)*X 0 0+(5128273171/10000000000 : ℝ)*X 0 1+(678327973/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((131398361/250000000 : ℝ)*X 1 0+(-1873583727/10000000000 : ℝ)*X 1 1+(5426623591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((210237369/400000000 : ℝ)*X 2 0+(169581973/312500000 : ℝ)*X 2 1+(-468396161/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2269471063/5000000000 : ℝ)*X 0 0+(1040761853/2500000000 : ℝ)*X 0 1+(4163047937/10000000000 : ℝ)*X 0 2+(2269471063/5000000000 : ℝ)*X 1 0+(1040761853/2500000000 : ℝ)*X 1 1+(4163047937/10000000000 : ℝ)*X 1 2+(2269471063/5000000000 : ℝ)*X 2 0+(1040761853/2500000000 : ℝ)*X 2 1+(4163047937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1787838153/10000000000 : ℝ)*X 0 0+(5516550151/10000000000 : ℝ)*X 0 1+(1045505067/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((674360277/1250000000 : ℝ)*X 1 0+(-1955194149/10000000000 : ℝ)*X 1 1+(2613762787/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697441117/5000000000 : ℝ)*X 2 0+(2613762713/5000000000 : ℝ)*X 2 1+(-488798581/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2019308589/5000000000 : ℝ)*X 0 0+(441319931/1000000000 : ℝ)*X 0 1+(1103299811/2500000000 : ℝ)*X 0 2+(2019308589/5000000000 : ℝ)*X 1 0+(441319931/1000000000 : ℝ)*X 1 1+(1103299811/2500000000 : ℝ)*X 1 2+(2019308589/5000000000 : ℝ)*X 2 0+(441319931/1000000000 : ℝ)*X 2 1+(1103299811/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1482_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7963/12500 : ℝ) ≤ (-7454678681595428001398207877/11702500000000000000000000000 : ℝ) := by norm_num
    linear_combination (27445789/100000000000000 : ℝ)*(upper1) + (81686747/100000000000000 : ℝ)*(lower4) + (5639993/25000000000000 : ℝ)*(upper5) + (1089368117806223/50000000000000 : ℝ)*(major0) + (1089368117806223/50000000000000 : ℝ)*(major1) + (1089368117806223/50000000000000 : ℝ)*(major2) + (5327126419/50000000000000 : ℝ)*(sp2) + (472711833/50000000000000 : ℝ)*(sp3) + (3025331506557163/100000000000000 : ℝ)*(sp4) + (302531986166159/10000000000000 : ℝ)*(sp5) + (756332797707237/25000000000000 : ℝ)*(sp6) + (1353363544371343/100000000000000 : ℝ)*(sp7) + (10338524623/100000000000000 : ℝ)*(sp12) + (5495855049/25000000000000 : ℝ)*(sp13) + (21146320153047/1562500000000 : ℝ)*(f.failure) + (1512670922540893/50000000000000 : ℝ)*(f.sum) + (76625034664753/11702500000000000000000000000 : ℝ)*base66 + (386797919867509019/2340500000000000000000000000000000 : ℝ)*base67 + (1395254567232490981/2340500000000000000000000000000000 : ℝ)*base70 + (6526053614947990981/2340500000000000000000000000000000 : ℝ)*base72 + (178537616169371/23405000000000000000000000000 : ℝ)*base74 + (3645564043369990981/2340500000000000000000000000000000 : ℝ)*base76 + (8238851632757009019/2340500000000000000000000000000000 : ℝ)*base77 + (13746300263119509019/2340500000000000000000000000000000 : ℝ)*base79 + (3706309196253/731406250000000000000000000 : ℝ)*base82 + (266771/19531250000000000000 : ℝ)*base90 + (266771/19531250000000000000 : ℝ)*base92 + (266771/19531250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58487/100000 : ℝ) ≤ (342236992808849475570642954792573/585125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (67542169/100000000000000 : ℝ)*(lower3) + (1951637/12500000000000 : ℝ)*(upper4) + (3893113/10000000000000 : ℝ)*(upper5) + (563233583725653/25000000000000 : ℝ)*(major0) + (563233583725653/25000000000000 : ℝ)*(major1) + (563233583725653/25000000000000 : ℝ)*(major2) + (771729364453437/25000000000000 : ℝ)*(sp0) + (3086916990537957/100000000000000 : ℝ)*(sp1) + (3086892531592659/100000000000000 : ℝ)*(sp2) + (1399453512363691/100000000000000 : ℝ)*(sp3) + (1076089899/100000000000000 : ℝ)*(sp5) + (286692631/50000000000000 : ℝ)*(sp7) + (25535035197/100000000000000 : ℝ)*(sp10) + (152203527/25000000000000 : ℝ)*(sp12) + (174931760718619/12500000000000 : ℝ)*(f.failure) + (192932379164241/6250000000000 : ℝ)*(f.sum) + (33932288603073/23405000000000000000000000000 : ℝ)*base65 + (2489914213579839191/1170250000000000000000000000000000 : ℝ)*base68 + (1975897129300660809/1170250000000000000000000000000000 : ℝ)*base69 + (9353090656674660809/1170250000000000000000000000000000 : ℝ)*base71 + (31549834621501/11702500000000000000000000000 : ℝ)*base74 + (3843055310393160809/1170250000000000000000000000000000 : ℝ)*base75 + (7096730421636160809/1170250000000000000000000000000000 : ℝ)*base77 + (117880816233839191/1170250000000000000000000000000000 : ℝ)*base80 + (11798203576207/5851250000000000000000000000 : ℝ)*base81 + (632873/39062500000000000000 : ℝ)*base90 + (632873/39062500000000000000 : ℝ)*base92 + (632873/39062500000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (7999/10000 : ℝ) ≤ (18722329794877777750670971491/23405000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8938827/5000000000000 : ℝ)*(upper0) + (76485243/50000000000000 : ℝ)*(upper2) + (357333787/100000000000000 : ℝ)*(lower5) + (153137888642091/6250000000000 : ℝ)*(major0) + (153137888642091/6250000000000 : ℝ)*(major1) + (153137888642091/6250000000000 : ℝ)*(major2) + (56417419469/100000000000000 : ℝ)*(sp1) + (20793700559/100000000000000 : ℝ)*(sp3) + (14279741/156250000000 : ℝ)*(sp4) + (1675872514364883/50000000000000 : ℝ)*(sp8) + (104740574031507/3125000000000 : ℝ)*(sp9) + (3351754786427693/100000000000000 : ℝ)*(sp10) + (760986284226647/50000000000000 : ℝ)*(sp11) + (309331843/50000000000000 : ℝ)*(sp12) + (380498340538463/25000000000000 : ℝ)*(f.failure) + (3351754786427693/100000000000000 : ℝ)*(f.sum) + (106809356396121/23405000000000000000000000000 : ℝ)*base66 + (2177942448173109723/292562500000000000000000000000000 : ℝ)*base67 + (511980432190109723/292562500000000000000000000000000 : ℝ)*base69 + (904963609416015277/292562500000000000000000000000000 : ℝ)*base72 + (178243079414991/23405000000000000000000000000 : ℝ)*base74 + (521996729094952777/292562500000000000000000000000000 : ℝ)*base76 + (691984858065047223/292562500000000000000000000000000 : ℝ)*base77 + (2612393364519140277/292562500000000000000000000000000 : ℝ)*base80 + (101577859561721/23405000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (70321/78125000000000000000 : ℝ)*base90 + (70321/78125000000000000000 : ℝ)*base92 + (70321/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-85807/100000 : ℝ) ≤ (-200824905500911940058804795824133/234050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22513853/50000000000000 : ℝ)*(lower0) + (1532259/20000000000000 : ℝ)*(lower1) + (22018051/100000000000000 : ℝ)*(lower2) + (37211901/50000000000000 : ℝ)*(lower4) + (248857168786729/10000000000000 : ℝ)*(major0) + (248857168786729/10000000000000 : ℝ)*(major1) + (248857168786729/10000000000000 : ℝ)*(major2) + (150332893/1562500000000 : ℝ)*(sp0) + (64528710441/100000000000000 : ℝ)*(sp5) + (120565863077/100000000000000 : ℝ)*(sp6) + (172995517891881/5000000000000 : ℝ)*(sp12) + (345985545043233/10000000000000 : ℝ)*(sp13) + (1729899706639847/50000000000000 : ℝ)*(sp14) + (386456205393087/25000000000000 : ℝ)*(sp15) + (386456205393087/25000000000000 : ℝ)*(f.failure) + (3459919979142771/100000000000000 : ℝ)*(f.sum) + (2028291213439/468100000000000000000000000 : ℝ)*base65 + (1918151360200558237/468100000000000000000000000000000 : ℝ)*base67 + (1065402531806158237/468100000000000000000000000000000 : ℝ)*base69 + (4498564937145958237/468100000000000000000000000000000 : ℝ)*base71 + (8758832301853/4681000000000000000000000000 : ℝ)*base73 + (3453164073704858237/468100000000000000000000000000000 : ℝ)*base75 + (5858395922097558237/468100000000000000000000000000000 : ℝ)*base77 + (4835024122239758237/468100000000000000000000000000000 : ℝ)*base79 + (6002419760557/2340500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (261029/78125000000000000000 : ℝ)*base90 + (261029/78125000000000000000 : ℝ)*base92 + (261029/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1482_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2159/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7963/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58487/100000 : ℝ) else (7999/10000 : ℝ) ≤ X j i ∧ X j i ≤ (85807/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1482_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1482_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10793/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7963/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58487/100000 : ℝ) else (7999/10000 : ℝ) ≤ X j i ∧ X j i ≤ (85807/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1482_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1482_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1482_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4459/1024 : ℝ) ≤ p) (hpb : p ≤ (4461/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (5030833/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10793/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7963/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58487/100000 : ℝ) else (7999/10000 : ℝ) ≤ X j i ∧ X j i ≤ (85807/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1482_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
