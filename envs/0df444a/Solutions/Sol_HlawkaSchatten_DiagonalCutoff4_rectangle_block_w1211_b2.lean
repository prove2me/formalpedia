-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1211_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:13.71607+00:00
-- url     : https://prove2.me/submissions/cd0c9805-9d49-4c52-94aa-0cf3a82e1d3c

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
theorem support_rectangle_w1211_s6_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067149167/5000000000 : ℝ)*x 0 + (5392002211/10000000000 : ℝ)*x 1 + (1316642857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067149167/5000000000 : ℝ)^2101 ≤ (6487851725323/50000000000000 : ℝ)^1589 := by
    have hnat : (1067149167 : ℕ)^2101*50000000000000^1589 ≤ 6487851725323^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067149167 5000000000 6487851725323 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392002211/10000000000 : ℝ)^2101 ≤ (1104729254471/2500000000000 : ℝ)^1589 := by
    have hnat : (5392002211 : ℕ)^2101*2500000000000^1589 ≤ 1104729254471^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392002211 10000000000 1104729254471 2500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316642857/2500000000 : ℝ)^2101 ≤ (21417563180341/50000000000000 : ℝ)^1589 := by
    have hnat : (1316642857 : ℕ)^2101*50000000000000^1589 ≤ 21417563180341^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316642857 2500000000 21417563180341 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067149167/5000000000 : ℝ), (5392002211/10000000000 : ℝ), (1316642857/2500000000 : ℝ)] ![(6487851725323/50000000000000 : ℝ), (1104729254471/2500000000000 : ℝ), (21417563180341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067149167/5000000000 : ℝ)|^2101 ≤ (6487851725323/50000000000000 : ℝ)^1589
        have hw : |(-1067149167/5000000000 : ℝ)|=(1067149167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392002211/10000000000 : ℝ)|^2101 ≤ (1104729254471/2500000000000 : ℝ)^1589
        have hw : |(5392002211/10000000000 : ℝ)|=(5392002211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316642857/2500000000 : ℝ)|^2101 ≤ (21417563180341/50000000000000 : ℝ)^1589
        have hw : |(1316642857/2500000000 : ℝ)|=(1316642857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s6_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344523521/10000000000 : ℝ)*x 0 + (-2197905679/10000000000 : ℝ)*x 1 + (2633285563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344523521/10000000000 : ℝ)^2101 ≤ (43675423649393/100000000000000 : ℝ)^1589 := by
    have hnat : (5344523521 : ℕ)^2101*100000000000000^1589 ≤ 43675423649393^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344523521 10000000000 43675423649393 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197905679/10000000000 : ℝ)^2101 ≤ (3372363305393/25000000000000 : ℝ)^1589 := by
    have hnat : (2197905679 : ℕ)^2101*25000000000000^1589 ≤ 3372363305393^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197905679 10000000000 3372363305393 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633285563/5000000000 : ℝ)^2101 ≤ (42835123112943/100000000000000 : ℝ)^1589 := by
    have hnat : (2633285563 : ℕ)^2101*100000000000000^1589 ≤ 42835123112943^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633285563 5000000000 42835123112943 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344523521/10000000000 : ℝ), (-2197905679/10000000000 : ℝ), (2633285563/5000000000 : ℝ)] ![(43675423649393/100000000000000 : ℝ), (3372363305393/25000000000000 : ℝ), (42835123112943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344523521/10000000000 : ℝ)|^2101 ≤ (43675423649393/100000000000000 : ℝ)^1589
        have hw : |(5344523521/10000000000 : ℝ)|=(5344523521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197905679/10000000000 : ℝ)|^2101 ≤ (3372363305393/25000000000000 : ℝ)^1589
        have hw : |(-2197905679/10000000000 : ℝ)|=(2197905679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633285563/5000000000 : ℝ)|^2101 ≤ (42835123112943/100000000000000 : ℝ)^1589
        have hw : |(2633285563/5000000000 : ℝ)|=(2633285563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s6_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344523383/10000000000 : ℝ)*x 0 + (2633285617/5000000000 : ℝ)*x 1 + (-54947643/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344523383/10000000000 : ℝ)^2101 ≤ (10918855539571/25000000000000 : ℝ)^1589 := by
    have hnat : (5344523383 : ℕ)^2101*25000000000000^1589 ≤ 10918855539571^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344523383 10000000000 10918855539571 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633285617/5000000000 : ℝ)^2101 ≤ (21417562137193/50000000000000 : ℝ)^1589 := by
    have hnat : (2633285617 : ℕ)^2101*50000000000000^1589 ≤ 21417562137193^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633285617 5000000000 21417562137193 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54947643/250000000 : ℝ)^2101 ≤ (6744726777143/50000000000000 : ℝ)^1589 := by
    have hnat : (54947643 : ℕ)^2101*50000000000000^1589 ≤ 6744726777143^1589*250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54947643 250000000 6744726777143 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344523383/10000000000 : ℝ), (2633285617/5000000000 : ℝ), (-54947643/250000000 : ℝ)] ![(10918855539571/25000000000000 : ℝ), (21417562137193/50000000000000 : ℝ), (6744726777143/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344523383/10000000000 : ℝ)|^2101 ≤ (10918855539571/25000000000000 : ℝ)^1589
        have hw : |(5344523383/10000000000 : ℝ)|=(5344523383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633285617/5000000000 : ℝ)|^2101 ≤ (21417562137193/50000000000000 : ℝ)^1589
        have hw : |(2633285617/5000000000 : ℝ)|=(2633285617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54947643/250000000 : ℝ)|^2101 ≤ (6744726777143/50000000000000 : ℝ)^1589
        have hw : |(-54947643/250000000 : ℝ)|=(54947643/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s6_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4355030811/10000000000 : ℝ)*x 0 + (4230367421/10000000000 : ℝ)*x 1 + (2241645467/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355030811/10000000000 : ℝ)^2101 ≤ (1332688653311/4000000000000 : ℝ)^1589 := by
    have hnat : (4355030811 : ℕ)^2101*4000000000000^1589 ≤ 1332688653311^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355030811 10000000000 1332688653311 4000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230367421/10000000000 : ℝ)^2101 ≤ (1282482389561/4000000000000 : ℝ)^1589 := by
    have hnat : (4230367421 : ℕ)^2101*4000000000000^1589 ≤ 1282482389561^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230367421 10000000000 1282482389561 4000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241645467/5000000000 : ℝ)^2101 ≤ (8655180980491/25000000000000 : ℝ)^1589 := by
    have hnat : (2241645467 : ℕ)^2101*25000000000000^1589 ≤ 8655180980491^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241645467 5000000000 8655180980491 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355030811/10000000000 : ℝ), (4230367421/10000000000 : ℝ), (2241645467/5000000000 : ℝ)] ![(1332688653311/4000000000000 : ℝ), (1282482389561/4000000000000 : ℝ), (8655180980491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355030811/10000000000 : ℝ)|^2101 ≤ (1332688653311/4000000000000 : ℝ)^1589
        have hw : |(4355030811/10000000000 : ℝ)|=(4355030811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230367421/10000000000 : ℝ)|^2101 ≤ (1282482389561/4000000000000 : ℝ)^1589
        have hw : |(4230367421/10000000000 : ℝ)|=(4230367421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241645467/5000000000 : ℝ)|^2101 ≤ (8655180980491/25000000000000 : ℝ)^1589
        have hw : |(2241645467/5000000000 : ℝ)|=(2241645467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s6_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-133393953/625000000 : ℝ)*x 0 + (2633444149/5000000000 : ℝ)*x 1 + (5391684083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133393953/625000000 : ℝ)^2101 ≤ (3243935738029/25000000000000 : ℝ)^1589 := by
    have hnat : (133393953 : ℕ)^2101*25000000000000^1589 ≤ 3243935738029^1589*625000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133393953 625000000 3243935738029 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633444149/5000000000 : ℝ)^2101 ≤ (21419267023311/50000000000000 : ℝ)^1589 := by
    have hnat : (2633444149 : ℕ)^2101*50000000000000^1589 ≤ 21419267023311^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633444149 5000000000 21419267023311 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391684083/10000000000 : ℝ)^2101 ≤ (44185722984987/100000000000000 : ℝ)^1589 := by
    have hnat : (5391684083 : ℕ)^2101*100000000000000^1589 ≤ 44185722984987^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391684083 10000000000 44185722984987 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133393953/625000000 : ℝ), (2633444149/5000000000 : ℝ), (5391684083/10000000000 : ℝ)] ![(3243935738029/25000000000000 : ℝ), (21419267023311/50000000000000 : ℝ), (44185722984987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133393953/625000000 : ℝ)|^2101 ≤ (3243935738029/25000000000000 : ℝ)^1589
        have hw : |(-133393953/625000000 : ℝ)|=(133393953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633444149/5000000000 : ℝ)|^2101 ≤ (21419267023311/50000000000000 : ℝ)^1589
        have hw : |(2633444149/5000000000 : ℝ)|=(2633444149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391684083/10000000000 : ℝ)|^2101 ≤ (44185722984987/100000000000000 : ℝ)^1589
        have hw : |(5391684083/10000000000 : ℝ)|=(5391684083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s6_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (332036691/625000000 : ℝ)*x 0 + (-2072792819/10000000000 : ℝ)*x 1 + (67396051/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332036691/625000000 : ℝ)^2101 ≤ (43330678419357/100000000000000 : ℝ)^1589 := by
    have hnat : (332036691 : ℕ)^2101*100000000000000^1589 ≤ 43330678419357^1589*625000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332036691 625000000 43330678419357 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072792819/10000000000 : ℝ)^2101 ≤ (12483598612221/100000000000000 : ℝ)^1589 := by
    have hnat : (2072792819 : ℕ)^2101*100000000000000^1589 ≤ 12483598612221^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072792819 10000000000 12483598612221 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67396051/125000000 : ℝ)^2101 ≤ (276160768453/625000000000 : ℝ)^1589 := by
    have hnat : (67396051 : ℕ)^2101*625000000000^1589 ≤ 276160768453^1589*125000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67396051 125000000 276160768453 625000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332036691/625000000 : ℝ), (-2072792819/10000000000 : ℝ), (67396051/125000000 : ℝ)] ![(43330678419357/100000000000000 : ℝ), (12483598612221/100000000000000 : ℝ), (276160768453/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332036691/625000000 : ℝ)|^2101 ≤ (43330678419357/100000000000000 : ℝ)^1589
        have hw : |(332036691/625000000 : ℝ)|=(332036691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2072792819/10000000000 : ℝ)|^2101 ≤ (12483598612221/100000000000000 : ℝ)^1589
        have hw : |(-2072792819/10000000000 : ℝ)|=(2072792819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67396051/125000000 : ℝ)|^2101 ≤ (276160768453/625000000000 : ℝ)^1589
        have hw : |(67396051/125000000 : ℝ)|=(67396051/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s6_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312587057/10000000000 : ℝ)*x 0 + (5391684079/10000000000 : ℝ)*x 1 + (-2072792819/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312587057/10000000000 : ℝ)^2101 ≤ (43330678430141/100000000000000 : ℝ)^1589 := by
    have hnat : (5312587057 : ℕ)^2101*100000000000000^1589 ≤ 43330678430141^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312587057 10000000000 43330678430141 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391684079/10000000000 : ℝ)^2101 ≤ (11046430735411/25000000000000 : ℝ)^1589 := by
    have hnat : (5391684079 : ℕ)^2101*25000000000000^1589 ≤ 11046430735411^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391684079 10000000000 11046430735411 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2072792819/10000000000 : ℝ)^2101 ≤ (12483598612221/100000000000000 : ℝ)^1589 := by
    have hnat : (2072792819 : ℕ)^2101*100000000000000^1589 ≤ 12483598612221^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072792819 10000000000 12483598612221 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312587057/10000000000 : ℝ), (5391684079/10000000000 : ℝ), (-2072792819/10000000000 : ℝ)] ![(43330678430141/100000000000000 : ℝ), (11046430735411/25000000000000 : ℝ), (12483598612221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312587057/10000000000 : ℝ)|^2101 ≤ (43330678430141/100000000000000 : ℝ)^1589
        have hw : |(5312587057/10000000000 : ℝ)|=(5312587057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391684079/10000000000 : ℝ)|^2101 ≤ (11046430735411/25000000000000 : ℝ)^1589
        have hw : |(5391684079/10000000000 : ℝ)|=(5391684079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2072792819/10000000000 : ℝ)|^2101 ≤ (12483598612221/100000000000000 : ℝ)^1589
        have hw : |(-2072792819/10000000000 : ℝ)|=(2072792819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s6_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (43550407/100000000 : ℝ)*x 0 + (4482651501/10000000000 : ℝ)*x 1 + (4231008917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (43550407/100000000 : ℝ)^2101 ≤ (8329329090803/25000000000000 : ℝ)^1589 := by
    have hnat : (43550407 : ℕ)^2101*25000000000000^1589 ≤ 8329329090803^1589*100000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43550407 100000000 8329329090803 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482651501/10000000000 : ℝ)^2101 ≤ (8653548806503/25000000000000 : ℝ)^1589 := by
    have hnat : (4482651501 : ℕ)^2101*25000000000000^1589 ≤ 8653548806503^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482651501 10000000000 8653548806503 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231008917/10000000000 : ℝ)^2101 ≤ (32068488392959/100000000000000 : ℝ)^1589 := by
    have hnat : (4231008917 : ℕ)^2101*100000000000000^1589 ≤ 32068488392959^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231008917 10000000000 32068488392959 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(43550407/100000000 : ℝ), (4482651501/10000000000 : ℝ), (4231008917/10000000000 : ℝ)] ![(8329329090803/25000000000000 : ℝ), (8653548806503/25000000000000 : ℝ), (32068488392959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(43550407/100000000 : ℝ)|^2101 ≤ (8329329090803/25000000000000 : ℝ)^1589
        have hw : |(43550407/100000000 : ℝ)|=(43550407/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482651501/10000000000 : ℝ)|^2101 ≤ (8653548806503/25000000000000 : ℝ)^1589
        have hw : |(4482651501/10000000000 : ℝ)|=(4482651501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231008917/10000000000 : ℝ)|^2101 ≤ (32068488392959/100000000000000 : ℝ)^1589
        have hw : |(4231008917/10000000000 : ℝ)|=(4231008917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2859/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14093/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11413/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14117/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11413/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14117/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11413/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11413/100000 : ℝ) ^ (8403/2048 : ℝ) ≤ (13567057824403603/100000000000000000000 : ℝ) := by
    have hpowers : (11413/100000 : ℝ)^8403 ≤ (13567057824403603/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11413 : ℕ)^8403*100000000000000000000^2048 ≤ 13567057824403603^2048*100000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11413 100000 13567057824403603 100000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11413/100000 : ℝ)) (X := (13567057824403603/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14117/100000 : ℝ) ^ (8403/2048 : ℝ) ≤ (32461596739381881/100000000000000000000 : ℝ) := by
    have hpowers : (14117/100000 : ℝ)^8403 ≤ (32461596739381881/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14117 : ℕ)^8403*100000000000000000000^2048 ≤ 32461596739381881^2048*100000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14117 100000 32461596739381881 100000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14117/100000 : ℝ)) (X := (32461596739381881/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013567057824403603/50000000000000000000 : ℝ) ≤ (5000330625776197/5000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (50013567057824403603/50000000000000000000 : ℝ)^2048 ≤ (5000330625776197/5000000000000000 : ℝ)^8403 := by
      have hnat : (50013567057824403603 : ℕ)^2048*5000000000000000^8403 ≤ 5000330625776197^8403*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013567057824403603 50000000000000000000 5000330625776197 5000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000330625776197/5000000000000000 : ℝ)) (X := (50013567057824403603/50000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011507163640946371/25000000000000000000 : ℝ) ≤ (10001121626581509/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (25011507163640946371/25000000000000000000 : ℝ)^2048 ≤ (10001121626581509/10000000000000000 : ℝ)^8403 := by
      have hnat : (25011507163640946371 : ℕ)^2048*10000000000000000^8403 ≤ 10001121626581509^8403*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011507163640946371 25000000000000000000 10001121626581509 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001121626581509/10000000000000000 : ℝ)) (X := (25011507163640946371/25000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032461596739381881/50000000000000000000 : ℝ) ≤ (78137359387583/78125000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (50032461596739381881/50000000000000000000 : ℝ)^2048 ≤ (78137359387583/78125000000000 : ℝ)^8403 := by
      have hnat : (50032461596739381881 : ℕ)^2048*78125000000000^8403 ≤ 78137359387583^8403*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032461596739381881 50000000000000000000 78137359387583 78125000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78137359387583/78125000000000 : ℝ)) (X := (50032461596739381881/50000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13567057824403603/100000000000000000000 : ℝ) ≤ ((13515639751891547193/13520000000000000000 : ℝ)+2*(92075005823/54080000000000 : ℝ)*(11413/100000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (13515639751891547193/13520000000000000000 : ℝ)+2*(92075005823/54080000000000 : ℝ)*(11413/100000 : ℝ)=(5000330625776197/5000000000000000 : ℝ) by norm_num, show 1+2*(13567057824403603/100000000000000000000 : ℝ)=(50013567057824403603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32461596739381881/100000000000000000000 : ℝ)+(13567057824403603/100000000000000000000 : ℝ) ≤ ((13515639751891547193/13520000000000000000 : ℝ)+(92075005823/54080000000000 : ℝ)*((14117/100000 : ℝ)+(11413/100000 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (13515639751891547193/13520000000000000000 : ℝ)+(92075005823/54080000000000 : ℝ)*((14117/100000 : ℝ)+(11413/100000 : ℝ))=(10001121626581509/10000000000000000 : ℝ) by norm_num, show 1+(32461596739381881/100000000000000000000 : ℝ)+(13567057824403603/100000000000000000000 : ℝ)=(25011507163640946371/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32461596739381881/100000000000000000000 : ℝ) ≤ ((13515639751891547193/13520000000000000000 : ℝ)+2*(92075005823/54080000000000 : ℝ)*(14117/100000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (13515639751891547193/13520000000000000000 : ℝ)+2*(92075005823/54080000000000 : ℝ)*(14117/100000 : ℝ)=(78137359387583/78125000000000 : ℝ) by norm_num, show 1+2*(32461596739381881/100000000000000000000 : ℝ)=(50032461596739381881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13515639751891547193/13520000000000000000 : ℝ)*(X 1 0+X 2 0)+(92075005823/54080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13515639751891547193/13520000000000000000 : ℝ)) (alpha := (92075005823/54080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13515639751891547193/13520000000000000000 : ℝ)*(X 0 1+X 2 1)+(92075005823/54080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13515639751891547193/13520000000000000000 : ℝ)) (alpha := (92075005823/54080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13515639751891547193/13520000000000000000 : ℝ)*(X 0 2+X 1 2)+(92075005823/54080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (11413/100000 : ℝ)) (hi := (14117/100000 : ℝ)) (c := (13515639751891547193/13520000000000000000 : ℝ)) (alpha := (92075005823/54080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1067149167/5000000000 : ℝ)*X 0 0+(5392002211/10000000000 : ℝ)*X 0 1+(1316642857/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344523521/10000000000 : ℝ)*X 1 0+(-2197905679/10000000000 : ℝ)*X 1 1+(2633285563/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344523383/10000000000 : ℝ)*X 2 0+(2633285617/5000000000 : ℝ)*X 2 1+(-54947643/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355030811/10000000000 : ℝ)*X 0 0+(4230367421/10000000000 : ℝ)*X 0 1+(2241645467/5000000000 : ℝ)*X 0 2+(4355030811/10000000000 : ℝ)*X 1 0+(4230367421/10000000000 : ℝ)*X 1 1+(2241645467/5000000000 : ℝ)*X 1 2+(4355030811/10000000000 : ℝ)*X 2 0+(4230367421/10000000000 : ℝ)*X 2 1+(2241645467/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-133393953/625000000 : ℝ)*X 0 0+(2633444149/5000000000 : ℝ)*X 0 1+(5391684083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332036691/625000000 : ℝ)*X 1 0+(-2072792819/10000000000 : ℝ)*X 1 1+(67396051/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312587057/10000000000 : ℝ)*X 2 0+(5391684079/10000000000 : ℝ)*X 2 1+(-2072792819/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((43550407/100000000 : ℝ)*X 0 0+(4482651501/10000000000 : ℝ)*X 0 1+(4231008917/10000000000 : ℝ)*X 0 2+(43550407/100000000 : ℝ)*X 1 0+(4482651501/10000000000 : ℝ)*X 1 1+(4231008917/10000000000 : ℝ)*X 1 2+(43550407/100000000 : ℝ)*X 2 0+(4482651501/10000000000 : ℝ)*X 2 1+(4231008917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3370050001808919374703/540800000000000000000000000 : ℝ) := by norm_num
    linear_combination (15967281/2000000000000 : ℝ)*(base19) + (688418429/100000000000000 : ℝ)*(base23) + (734203/100000000000000 : ℝ)*(lower2) + (8337297/25000000000000 : ℝ)*(upper3) + (649933/1250000000000 : ℝ)*(lower4) + (5963164922614279/100000000000000 : ℝ)*(major0) + (5963164922614279/100000000000000 : ℝ)*(major1) + (5963164922614279/100000000000000 : ℝ)*(major2) + (7972538202820499/100000000000000 : ℝ)*(sp0) + (7972545699369007/100000000000000 : ℝ)*(sp1) + (7972545809314629/100000000000000 : ℝ)*(sp2) + (79075484966693/2000000000000 : ℝ)*(sp3) + (4147456279/50000000000000 : ℝ)*(sp4) + (11114301/125000000000 : ℝ)*(sp7) + (79075662795509/2000000000000 : ℝ)*(f.failure) + (7972546497733057/100000000000000 : ℝ)*(f.sum) + (888656419783/2704000000000000000000000000 : ℝ)*base66 + (7981705388777581153/1352000000000000000000000000000000 : ℝ)*base68 + (4350565389953581153/1352000000000000000000000000000000 : ℝ)*base70 + (4633229612774418847/1352000000000000000000000000000000 : ℝ)*base71 + (15865743586071/2704000000000000000000000000 : ℝ)*base74 + (8095980415454418847/1352000000000000000000000000000000 : ℝ)*base75 + (10407170450745581153/1352000000000000000000000000000000 : ℝ)*base78 + (15490079158446418847/1352000000000000000000000000000000 : ℝ)*base79 + (9752733537337/2704000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (6083/800000000000000000 : ℝ)*base89 + (6083/800000000000000000 : ℝ)*base91 + (6083/800000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (180673700942246656006509483/27040000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1209475309/100000000000000 : ℝ)*(base19) + (1316368331/100000000000000 : ℝ)*(base23) + (26662979/20000000000000 : ℝ)*(upper3) + (12029039/25000000000000 : ℝ)*(lower4) + (137337297/100000000000000 : ℝ)*(upper5) + (239739599629823/4000000000000 : ℝ)*(major0) + (239739599629823/4000000000000 : ℝ)*(major1) + (239739599629823/4000000000000 : ℝ)*(major2) + (33701195301/100000000000000 : ℝ)*(sp1) + (18082870007/50000000000000 : ℝ)*(sp2) + (8013090057351027/100000000000000 : ℝ)*(sp4) + (4006527573340209/50000000000000 : ℝ)*(sp5) + (4006526287621341/50000000000000 : ℝ)*(sp6) + (1986944850708063/50000000000000 : ℝ)*(sp7) + (1986944850708063/50000000000000 : ℝ)*(f.failure) + (8013090057351027/100000000000000 : ℝ)*(f.sum) + (17361469647591/2704000000000000000000000000 : ℝ)*base66 + (1117436105226839/54080000000000000000000000000000 : ℝ)*base67 + (110980328182346839/54080000000000000000000000000000 : ℝ)*base69 + (737528038593333161/54080000000000000000000000000000 : ℝ)*base72 + (529042060021/540800000000000000000000000 : ℝ)*base73 + (380726990257653161/54080000000000000000000000000000 : ℝ)*base76 + (489857039428106839/54080000000000000000000000000000 : ℝ)*base77 + (45937041464586839/54080000000000000000000000000000 : ℝ)*base79 + (17994536617191/2704000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (203081/20000000000000000000 : ℝ)*base89 + (203081/20000000000000000000 : ℝ)*base91 + (203081/20000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1211_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2859/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1211_s7_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-266789709/1250000000 : ℝ)*x 0 + (5391775807/10000000000 : ℝ)*x 1 + (2633392549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266789709/1250000000 : ℝ)^2101 ≤ (12975858900433/100000000000000 : ℝ)^1589 := by
    have hnat : (266789709 : ℕ)^2101*100000000000000^1589 ≤ 12975858900433^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266789709 1250000000 12975858900433 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391775807/10000000000 : ℝ)^2101 ≤ (44186716887661/100000000000000 : ℝ)^1589 := by
    have hnat : (5391775807 : ℕ)^2101*100000000000000^1589 ≤ 44186716887661^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391775807 10000000000 44186716887661 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633392549/5000000000 : ℝ)^2101 ≤ (21418712102543/50000000000000 : ℝ)^1589 := by
    have hnat : (2633392549 : ℕ)^2101*50000000000000^1589 ≤ 21418712102543^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633392549 5000000000 21418712102543 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266789709/1250000000 : ℝ), (5391775807/10000000000 : ℝ), (2633392549/5000000000 : ℝ)] ![(12975858900433/100000000000000 : ℝ), (44186716887661/100000000000000 : ℝ), (21418712102543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266789709/1250000000 : ℝ)|^2101 ≤ (12975858900433/100000000000000 : ℝ)^1589
        have hw : |(-266789709/1250000000 : ℝ)|=(266789709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391775807/10000000000 : ℝ)|^2101 ≤ (44186716887661/100000000000000 : ℝ)^1589
        have hw : |(5391775807/10000000000 : ℝ)|=(5391775807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633392549/5000000000 : ℝ)|^2101 ≤ (21418712102543/50000000000000 : ℝ)^1589
        have hw : |(2633392549/5000000000 : ℝ)|=(2633392549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s7_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344466189/10000000000 : ℝ)*x 0 + (-2197698451/10000000000 : ℝ)*x 1 + (5266785099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344466189/10000000000 : ℝ)^2101 ≤ (21837402085167/50000000000000 : ℝ)^1589 := by
    have hnat : (5344466189 : ℕ)^2101*50000000000000^1589 ≤ 21837402085167^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344466189 10000000000 21837402085167 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197698451/10000000000 : ℝ)^2101 ≤ (6743885798027/50000000000000 : ℝ)^1589 := by
    have hnat : (2197698451 : ℕ)^2101*50000000000000^1589 ≤ 6743885798027^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197698451 10000000000 6743885798027 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266785099/10000000000 : ℝ)^2101 ≤ (267733901349/625000000000 : ℝ)^1589 := by
    have hnat : (5266785099 : ℕ)^2101*625000000000^1589 ≤ 267733901349^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266785099 10000000000 267733901349 625000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344466189/10000000000 : ℝ), (-2197698451/10000000000 : ℝ), (5266785099/10000000000 : ℝ)] ![(21837402085167/50000000000000 : ℝ), (6743885798027/50000000000000 : ℝ), (267733901349/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344466189/10000000000 : ℝ)|^2101 ≤ (21837402085167/50000000000000 : ℝ)^1589
        have hw : |(5344466189/10000000000 : ℝ)|=(5344466189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197698451/10000000000 : ℝ)|^2101 ≤ (6743885798027/50000000000000 : ℝ)^1589
        have hw : |(-2197698451/10000000000 : ℝ)|=(2197698451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266785099/10000000000 : ℝ)|^2101 ≤ (267733901349/625000000000 : ℝ)^1589
        have hw : |(5266785099/10000000000 : ℝ)|=(5266785099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s7_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344466191/10000000000 : ℝ)*x 0 + (2633392561/5000000000 : ℝ)*x 1 + (-1098849209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344466191/10000000000 : ℝ)^2101 ≤ (5459350523993/12500000000000 : ℝ)^1589 := by
    have hnat : (5344466191 : ℕ)^2101*12500000000000^1589 ≤ 5459350523993^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344466191 10000000000 5459350523993 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633392561/5000000000 : ℝ)^2101 ≤ (10709356115797/25000000000000 : ℝ)^1589 := by
    have hnat : (2633392561 : ℕ)^2101*25000000000000^1589 ≤ 10709356115797^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633392561 5000000000 10709356115797 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098849209/5000000000 : ℝ)^2101 ≤ (3371942832067/25000000000000 : ℝ)^1589 := by
    have hnat : (1098849209 : ℕ)^2101*25000000000000^1589 ≤ 3371942832067^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098849209 5000000000 3371942832067 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344466191/10000000000 : ℝ), (2633392561/5000000000 : ℝ), (-1098849209/5000000000 : ℝ)] ![(5459350523993/12500000000000 : ℝ), (10709356115797/25000000000000 : ℝ), (3371942832067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344466191/10000000000 : ℝ)|^2101 ≤ (5459350523993/12500000000000 : ℝ)^1589
        have hw : |(5344466191/10000000000 : ℝ)|=(5344466191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633392561/5000000000 : ℝ)|^2101 ≤ (10709356115797/25000000000000 : ℝ)^1589
        have hw : |(2633392561/5000000000 : ℝ)|=(2633392561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1098849209/5000000000 : ℝ)|^2101 ≤ (3371942832067/25000000000000 : ℝ)^1589
        have hw : |(-1098849209/5000000000 : ℝ)|=(1098849209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s7_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4355042221/10000000000 : ℝ)*x 0 + (4230809859/10000000000 : ℝ)*x 1 + (2241422689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355042221/10000000000 : ℝ)^2101 ≤ (16658665874313/50000000000000 : ℝ)^1589 := by
    have hnat : (4355042221 : ℕ)^2101*50000000000000^1589 ≤ 16658665874313^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355042221 10000000000 16658665874313 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230809859/10000000000 : ℝ)^2101 ≤ (8016623382521/25000000000000 : ℝ)^1589 := by
    have hnat : (4230809859 : ℕ)^2101*25000000000000^1589 ≤ 8016623382521^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230809859 10000000000 8016623382521 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241422689/5000000000 : ℝ)^2101 ≤ (4327021838033/12500000000000 : ℝ)^1589 := by
    have hnat : (2241422689 : ℕ)^2101*12500000000000^1589 ≤ 4327021838033^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241422689 5000000000 4327021838033 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355042221/10000000000 : ℝ), (4230809859/10000000000 : ℝ), (2241422689/5000000000 : ℝ)] ![(16658665874313/50000000000000 : ℝ), (8016623382521/25000000000000 : ℝ), (4327021838033/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355042221/10000000000 : ℝ)|^2101 ≤ (16658665874313/50000000000000 : ℝ)^1589
        have hw : |(4355042221/10000000000 : ℝ)|=(4355042221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230809859/10000000000 : ℝ)|^2101 ≤ (8016623382521/25000000000000 : ℝ)^1589
        have hw : |(4230809859/10000000000 : ℝ)|=(4230809859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241422689/5000000000 : ℝ)|^2101 ≤ (4327021838033/12500000000000 : ℝ)^1589
        have hw : |(2241422689/5000000000 : ℝ)|=(2241422689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s7_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-266790347/1250000000 : ℝ)*x 0 + (2633550013/5000000000 : ℝ)*x 1 + (5391459457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (266790347/1250000000 : ℝ)^2101 ≤ (12975899929349/100000000000000 : ℝ)^1589 := by
    have hnat : (266790347 : ℕ)^2101*100000000000000^1589 ≤ 12975899929349^1589*1250000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266790347 1250000000 12975899929349 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633550013/5000000000 : ℝ)^2101 ≤ (1713632442017/4000000000000 : ℝ)^1589 := by
    have hnat : (2633550013 : ℕ)^2101*4000000000000^1589 ≤ 1713632442017^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633550013 5000000000 1713632442017 4000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391459457/10000000000 : ℝ)^2101 ≤ (5522911125773/12500000000000 : ℝ)^1589 := by
    have hnat : (5391459457 : ℕ)^2101*12500000000000^1589 ≤ 5522911125773^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391459457 10000000000 5522911125773 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-266790347/1250000000 : ℝ), (2633550013/5000000000 : ℝ), (5391459457/10000000000 : ℝ)] ![(12975899929349/100000000000000 : ℝ), (1713632442017/4000000000000 : ℝ), (5522911125773/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-266790347/1250000000 : ℝ)|^2101 ≤ (12975899929349/100000000000000 : ℝ)^1589
        have hw : |(-266790347/1250000000 : ℝ)|=(266790347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633550013/5000000000 : ℝ)|^2101 ≤ (1713632442017/4000000000000 : ℝ)^1589
        have hw : |(2633550013/5000000000 : ℝ)|=(2633550013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391459457/10000000000 : ℝ)|^2101 ≤ (5522911125773/12500000000000 : ℝ)^1589
        have hw : |(5391459457/10000000000 : ℝ)|=(5391459457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s7_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2656321007/5000000000 : ℝ)*x 0 + (-129563977/625000000 : ℝ)*x 1 + (1078291951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656321007/5000000000 : ℝ)^2101 ≤ (4333127110339/10000000000000 : ℝ)^1589 := by
    have hnat : (2656321007 : ℕ)^2101*10000000000000^1589 ≤ 4333127110339^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656321007 5000000000 4333127110339 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129563977/625000000 : ℝ)^2101 ≤ (6242718324321/50000000000000 : ℝ)^1589 := by
    have hnat : (129563977 : ℕ)^2101*50000000000000^1589 ≤ 6242718324321^1589*625000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129563977 625000000 6242718324321 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078291951/2000000000 : ℝ)^2101 ≤ (27614557647/62500000000 : ℝ)^1589 := by
    have hnat : (1078291951 : ℕ)^2101*62500000000^1589 ≤ 27614557647^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078291951 2000000000 27614557647 62500000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656321007/5000000000 : ℝ), (-129563977/625000000 : ℝ), (1078291951/2000000000 : ℝ)] ![(4333127110339/10000000000000 : ℝ), (6242718324321/50000000000000 : ℝ), (27614557647/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656321007/5000000000 : ℝ)|^2101 ≤ (4333127110339/10000000000000 : ℝ)^1589
        have hw : |(2656321007/5000000000 : ℝ)|=(2656321007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129563977/625000000 : ℝ)|^2101 ≤ (6242718324321/50000000000000 : ℝ)^1589
        have hw : |(-129563977/625000000 : ℝ)|=(129563977/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078291951/2000000000 : ℝ)|^2101 ≤ (27614557647/62500000000 : ℝ)^1589
        have hw : |(1078291951/2000000000 : ℝ)|=(1078291951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s7_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312641557/10000000000 : ℝ)*x 0 + (5391460121/10000000000 : ℝ)*x 1 + (-2073023753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312641557/10000000000 : ℝ)^2101 ≤ (43331266174953/100000000000000 : ℝ)^1589 := by
    have hnat : (5312641557 : ℕ)^2101*100000000000000^1589 ≤ 43331266174953^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312641557 10000000000 43331266174953 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391460121/10000000000 : ℝ)^2101 ≤ (44183296201037/100000000000000 : ℝ)^1589 := by
    have hnat : (5391460121 : ℕ)^2101*100000000000000^1589 ≤ 44183296201037^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391460121 10000000000 44183296201037 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2073023753/10000000000 : ℝ)^2101 ≤ (12485437612221/100000000000000 : ℝ)^1589 := by
    have hnat : (2073023753 : ℕ)^2101*100000000000000^1589 ≤ 12485437612221^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073023753 10000000000 12485437612221 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312641557/10000000000 : ℝ), (5391460121/10000000000 : ℝ), (-2073023753/10000000000 : ℝ)] ![(43331266174953/100000000000000 : ℝ), (44183296201037/100000000000000 : ℝ), (12485437612221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312641557/10000000000 : ℝ)|^2101 ≤ (43331266174953/100000000000000 : ℝ)^1589
        have hw : |(5312641557/10000000000 : ℝ)|=(5312641557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391460121/10000000000 : ℝ)|^2101 ≤ (44183296201037/100000000000000 : ℝ)^1589
        have hw : |(5391460121/10000000000 : ℝ)|=(5391460121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2073023753/10000000000 : ℝ)|^2101 ≤ (12485437612221/100000000000000 : ℝ)^1589
        have hw : |(-2073023753/10000000000 : ℝ)|=(2073023753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s7_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4355052131/10000000000 : ℝ)*x 0 + (2241105119/5000000000 : ℝ)*x 1 + (4231446919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355052131/10000000000 : ℝ)^2101 ≤ (3331743199157/10000000000000 : ℝ)^1589 := by
    have hnat : (4355052131 : ℕ)^2101*10000000000000^1589 ≤ 3331743199157^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355052131 10000000000 3331743199157 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241105119/5000000000 : ℝ)^2101 ≤ (17304845023547/50000000000000 : ℝ)^1589 := by
    have hnat : (2241105119 : ℕ)^2101*50000000000000^1589 ≤ 17304845023547^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241105119 5000000000 17304845023547 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231446919/10000000000 : ℝ)^2101 ≤ (32072877943363/100000000000000 : ℝ)^1589 := by
    have hnat : (4231446919 : ℕ)^2101*100000000000000^1589 ≤ 32072877943363^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231446919 10000000000 32072877943363 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355052131/10000000000 : ℝ), (2241105119/5000000000 : ℝ), (4231446919/10000000000 : ℝ)] ![(3331743199157/10000000000000 : ℝ), (17304845023547/50000000000000 : ℝ), (32072877943363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355052131/10000000000 : ℝ)|^2101 ≤ (3331743199157/10000000000000 : ℝ)^1589
        have hw : |(4355052131/10000000000 : ℝ)|=(4355052131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241105119/5000000000 : ℝ)|^2101 ≤ (17304845023547/50000000000000 : ℝ)^1589
        have hw : |(2241105119/5000000000 : ℝ)|=(2241105119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231446919/10000000000 : ℝ)|^2101 ≤ (32072877943363/100000000000000 : ℝ)^1589
        have hw : |(4231446919/10000000000 : ℝ)|=(4231446919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2859/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (143/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1761/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2859/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2859/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2859/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14093/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2859/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2859/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14093/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2859/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2859/25000 : ℝ) ^ (8403/2048 : ℝ) ≤ (854974360201457/6250000000000000000 : ℝ) := by
    have hpowers : (2859/25000 : ℝ)^8403 ≤ (854974360201457/6250000000000000000 : ℝ)^2048 := by
      have hnat : (2859 : ℕ)^8403*6250000000000000000^2048 ≤ 854974360201457^2048*25000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2859 25000 854974360201457 6250000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2859/25000 : ℝ)) (X := (854974360201457/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14093/100000 : ℝ) ^ (8403/2048 : ℝ) ≤ (16117879261472389/50000000000000000000 : ℝ) := by
    have hpowers : (14093/100000 : ℝ)^8403 ≤ (16117879261472389/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14093 : ℕ)^8403*50000000000000000000^2048 ≤ 16117879261472389^2048*100000^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14093 100000 16117879261472389 50000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14093/100000 : ℝ)) (X := (16117879261472389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125854974360201457/3125000000000000000 : ℝ) ≤ (5000333367867501/5000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (3125854974360201457/3125000000000000000 : ℝ)^2048 ≤ (5000333367867501/5000000000000000 : ℝ)^8403 := by
      have hnat : (3125854974360201457 : ℕ)^2048*5000000000000000^8403 ≤ 5000333367867501^8403*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125854974360201457 3125000000000000000 5000333367867501 5000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000333367867501/5000000000000000 : ℝ)) (X := (3125854974360201457/3125000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004591534828616809/10000000000000000000 : ℝ) ≤ (10001118866012539/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (10004591534828616809/10000000000000000000 : ℝ)^2048 ≤ (10001118866012539/10000000000000000 : ℝ)^8403 := by
      have hnat : (10004591534828616809 : ℕ)^2048*10000000000000000^8403 ≤ 10001118866012539^8403*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004591534828616809 10000000000000000000 10001118866012539 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001118866012539/10000000000000000 : ℝ)) (X := (10004591534828616809/10000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016117879261472389/25000000000000000000 : ℝ) ≤ (2500392749072519/2500000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (25016117879261472389/25000000000000000000 : ℝ)^2048 ≤ (2500392749072519/2500000000000000 : ℝ)^8403 := by
      have hnat : (25016117879261472389 : ℕ)^2048*2500000000000000^8403 ≤ 2500392749072519^8403*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016117879261472389 25000000000000000000 2500392749072519 2500000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500392749072519/2500000000000000 : ℝ)) (X := (25016117879261472389/25000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(854974360201457/6250000000000000000 : ℝ) ≤ ((531228607862801481/531400000000000000 : ℝ)+2*(452130277537/265700000000000 : ℝ)*(2859/25000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (531228607862801481/531400000000000000 : ℝ)+2*(452130277537/265700000000000 : ℝ)*(2859/25000 : ℝ)=(5000333367867501/5000000000000000 : ℝ) by norm_num, show 1+2*(854974360201457/6250000000000000000 : ℝ)=(3125854974360201457/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16117879261472389/50000000000000000000 : ℝ)+(854974360201457/6250000000000000000 : ℝ) ≤ ((531228607862801481/531400000000000000 : ℝ)+(452130277537/265700000000000 : ℝ)*((14093/100000 : ℝ)+(2859/25000 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (531228607862801481/531400000000000000 : ℝ)+(452130277537/265700000000000 : ℝ)*((14093/100000 : ℝ)+(2859/25000 : ℝ))=(10001118866012539/10000000000000000 : ℝ) by norm_num, show 1+(16117879261472389/50000000000000000000 : ℝ)+(854974360201457/6250000000000000000 : ℝ)=(10004591534828616809/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16117879261472389/50000000000000000000 : ℝ) ≤ ((531228607862801481/531400000000000000 : ℝ)+2*(452130277537/265700000000000 : ℝ)*(14093/100000 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (531228607862801481/531400000000000000 : ℝ)+2*(452130277537/265700000000000 : ℝ)*(14093/100000 : ℝ)=(2500392749072519/2500000000000000 : ℝ) by norm_num, show 1+2*(16117879261472389/50000000000000000000 : ℝ)=(25016117879261472389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (531228607862801481/531400000000000000 : ℝ)*(X 1 0+X 2 0)+(452130277537/265700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (2859/25000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (531228607862801481/531400000000000000 : ℝ)) (alpha := (452130277537/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (531228607862801481/531400000000000000 : ℝ)*(X 0 1+X 2 1)+(452130277537/265700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (2859/25000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (531228607862801481/531400000000000000 : ℝ)) (alpha := (452130277537/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (531228607862801481/531400000000000000 : ℝ)*(X 0 2+X 1 2)+(452130277537/265700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (2859/25000 : ℝ)) (hi := (14093/100000 : ℝ)) (c := (531228607862801481/531400000000000000 : ℝ)) (alpha := (452130277537/265700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-266789709/1250000000 : ℝ)*X 0 0+(5391775807/10000000000 : ℝ)*X 0 1+(2633392549/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344466189/10000000000 : ℝ)*X 1 0+(-2197698451/10000000000 : ℝ)*X 1 1+(5266785099/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344466191/10000000000 : ℝ)*X 2 0+(2633392561/5000000000 : ℝ)*X 2 1+(-1098849209/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355042221/10000000000 : ℝ)*X 0 0+(4230809859/10000000000 : ℝ)*X 0 1+(2241422689/5000000000 : ℝ)*X 0 2+(4355042221/10000000000 : ℝ)*X 1 0+(4230809859/10000000000 : ℝ)*X 1 1+(2241422689/5000000000 : ℝ)*X 1 2+(4355042221/10000000000 : ℝ)*X 2 0+(4230809859/10000000000 : ℝ)*X 2 1+(2241422689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-266790347/1250000000 : ℝ)*X 0 0+(2633550013/5000000000 : ℝ)*X 0 1+(5391459457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656321007/5000000000 : ℝ)*X 1 0+(-129563977/625000000 : ℝ)*X 1 1+(1078291951/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312641557/10000000000 : ℝ)*X 2 0+(5391460121/10000000000 : ℝ)*X 2 1+(-2073023753/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355052131/10000000000 : ℝ)*X 0 0+(2241105119/5000000000 : ℝ)*X 0 1+(4231446919/10000000000 : ℝ)*X 0 2+(4355052131/10000000000 : ℝ)*X 1 0+(2241105119/5000000000 : ℝ)*X 1 1+(4231446919/10000000000 : ℝ)*X 1 2+(4355052131/10000000000 : ℝ)*X 2 0+(2241105119/5000000000 : ℝ)*X 2 1+(4231446919/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (280849717507812829651898973/26570000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2022333847/100000000000000 : ℝ)*(base19) + (1894052943/100000000000000 : ℝ)*(base23) + (17539859/25000000000000 : ℝ)*(lower2) + (58310543/25000000000000 : ℝ)*(upper3) + (191239797/100000000000000 : ℝ)*(upper5) + (5984230731310711/100000000000000 : ℝ)*(major0) + (5984230731310711/100000000000000 : ℝ)*(major1) + (5984230731310711/100000000000000 : ℝ)*(major2) + (8000652482664829/100000000000000 : ℝ)*(sp0) + (4000354296766477/50000000000000 : ℝ)*(sp1) + (4000354360906929/50000000000000 : ℝ)*(sp2) + (991930435218639/25000000000000 : ℝ)*(sp3) + (14533300493/25000000000000 : ℝ)*(sp4) + (718838517/2500000000000 : ℝ)*(sp7) + (991937623603809/25000000000000 : ℝ)*(f.failure) + (8000710615866801/100000000000000 : ℝ)*(f.sum) + (34311132555947/13285000000000000000000000000 : ℝ)*base65 + (720210417168083009/53140000000000000000000000000000 : ℝ)*base68 + (1073849774017183009/53140000000000000000000000000000 : ℝ)*base70 + (648402973796896991/53140000000000000000000000000000 : ℝ)*base71 + (13178289899657/13285000000000000000000000000 : ℝ)*base73 + (943990758917183009/53140000000000000000000000000000 : ℝ)*base76 + (33786659920816991/53140000000000000000000000000000 : ℝ)*base77 + (406226212257223009/53140000000000000000000000000000 : ℝ)*base80 + (15028624749733/13285000000000000000000000000 : ℝ)*base82 + (20183/10000000000000000000 : ℝ)*base89 + (20183/10000000000000000000 : ℝ)*base91 + (20183/10000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33645724434238797027672021/13285000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (294579051/20000000000000 : ℝ)*(base19) + (530247867/50000000000000 : ℝ)*(base23) + (3483399/2500000000000 : ℝ)*(upper2) + (95106679/25000000000000 : ℝ)*(upper3) + (22949359/12500000000000 : ℝ)*(upper5) + (3007252382491149/50000000000000 : ℝ)*(major0) + (3007252382491149/50000000000000 : ℝ)*(major1) + (3007252382491149/50000000000000 : ℝ)*(major2) + (21575769971/50000000000000 : ℝ)*(sp1) + (2299780041/5000000000000 : ℝ)*(sp2) + (1005148278385979/12500000000000 : ℝ)*(sp4) + (1608228320530527/20000000000000 : ℝ)*(sp5) + (4020569585495639/50000000000000 : ℝ)*(sp6) + (1993911609228211/50000000000000 : ℝ)*(sp7) + (1993911609228211/50000000000000 : ℝ)*(f.failure) + (1005148278385979/12500000000000 : ℝ)*(f.sum) + (2139439137507/415156250000000000000000000 : ℝ)*base66 + (126571278180142331/26570000000000000000000000000000 : ℝ)*base68 + (427188482119322331/26570000000000000000000000000000 : ℝ)*base70 + (52776587623082331/26570000000000000000000000000000 : ℝ)*base72 + (1738180086877/415156250000000000000000000 : ℝ)*base74 + (344027077884952331/26570000000000000000000000000000 : ℝ)*base76 + (152636971077742331/26570000000000000000000000000000 : ℝ)*base78 + (386195809772362331/26570000000000000000000000000000 : ℝ)*base80 + (890122615843/6642500000000000000000000000 : ℝ)*base81 + (129557/20000000000000000000 : ℝ)*base89 + (129557/20000000000000000000 : ℝ)*base91 + (129557/20000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1211_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14093/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2859/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1211_s8_0 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2134323799/10000000000 : ℝ)*x 0 + (5391731577/10000000000 : ℝ)*x 1 + (5266825083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2134323799/10000000000 : ℝ)^2101 ≤ (12975908152821/100000000000000 : ℝ)^1589 := by
    have hnat : (2134323799 : ℕ)^2101*100000000000000^1589 ≤ 12975908152821^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134323799 10000000000 12975908152821 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391731577/10000000000 : ℝ)^2101 ≤ (8837247523933/20000000000000 : ℝ)^1589 := by
    have hnat : (5391731577 : ℕ)^2101*20000000000000^1589 ≤ 8837247523933^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391731577 10000000000 8837247523933 20000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266825083/10000000000 : ℝ)^2101 ≤ (21418927107039/50000000000000 : ℝ)^1589 := by
    have hnat : (5266825083 : ℕ)^2101*50000000000000^1589 ≤ 21418927107039^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266825083 10000000000 21418927107039 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2134323799/10000000000 : ℝ), (5391731577/10000000000 : ℝ), (5266825083/10000000000 : ℝ)] ![(12975908152821/100000000000000 : ℝ), (8837247523933/20000000000000 : ℝ), (21418927107039/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2134323799/10000000000 : ℝ)|^2101 ≤ (12975908152821/100000000000000 : ℝ)^1589
        have hw : |(-2134323799/10000000000 : ℝ)|=(2134323799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391731577/10000000000 : ℝ)|^2101 ≤ (8837247523933/20000000000000 : ℝ)^1589
        have hw : |(5391731577/10000000000 : ℝ)|=(5391731577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266825083/10000000000 : ℝ)|^2101 ≤ (21418927107039/50000000000000 : ℝ)^1589
        have hw : |(5266825083/10000000000 : ℝ)|=(5266825083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s8_1 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336113579/2500000000 : ℝ)*x 0 + (-2197661279/10000000000 : ℝ)*x 1 + (1316706269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336113579/2500000000 : ℝ)^2101 ≤ (10918668970357/25000000000000 : ℝ)^1589 := by
    have hnat : (1336113579 : ℕ)^2101*25000000000000^1589 ≤ 10918668970357^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336113579 2500000000 10918668970357 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2197661279/10000000000 : ℝ)^2101 ≤ (6743734978003/50000000000000 : ℝ)^1589 := by
    have hnat : (2197661279 : ℕ)^2101*50000000000000^1589 ≤ 6743734978003^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2197661279 10000000000 6743734978003 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316706269/2500000000 : ℝ)^2101 ≤ (42837854138799/100000000000000 : ℝ)^1589 := by
    have hnat : (1316706269 : ℕ)^2101*100000000000000^1589 ≤ 42837854138799^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316706269 2500000000 42837854138799 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336113579/2500000000 : ℝ), (-2197661279/10000000000 : ℝ), (1316706269/2500000000 : ℝ)] ![(10918668970357/25000000000000 : ℝ), (6743734978003/50000000000000 : ℝ), (42837854138799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336113579/2500000000 : ℝ)|^2101 ≤ (10918668970357/25000000000000 : ℝ)^1589
        have hw : |(1336113579/2500000000 : ℝ)|=(1336113579/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2197661279/10000000000 : ℝ)|^2101 ≤ (6743734978003/50000000000000 : ℝ)^1589
        have hw : |(-2197661279/10000000000 : ℝ)|=(2197661279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316706269/2500000000 : ℝ)|^2101 ≤ (42837854138799/100000000000000 : ℝ)^1589
        have hw : |(1316706269/2500000000 : ℝ)|=(1316706269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s8_2 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2672227159/5000000000 : ℝ)*x 0 + (5266825081/10000000000 : ℝ)*x 1 + (-219766127/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672227159/5000000000 : ℝ)^2101 ≤ (21837337951519/50000000000000 : ℝ)^1589 := by
    have hnat : (2672227159 : ℕ)^2101*50000000000000^1589 ≤ 21837337951519^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672227159 5000000000 21837337951519 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266825081/10000000000 : ℝ)^2101 ≤ (4283785419257/10000000000000 : ℝ)^1589 := by
    have hnat : (5266825081 : ℕ)^2101*10000000000000^1589 ≤ 4283785419257^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266825081 10000000000 4283785419257 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219766127/1000000000 : ℝ)^2101 ≤ (6743734941487/50000000000000 : ℝ)^1589 := by
    have hnat : (219766127 : ℕ)^2101*50000000000000^1589 ≤ 6743734941487^1589*1000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219766127 1000000000 6743734941487 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672227159/5000000000 : ℝ), (5266825081/10000000000 : ℝ), (-219766127/1000000000 : ℝ)] ![(21837337951519/50000000000000 : ℝ), (4283785419257/10000000000000 : ℝ), (6743734941487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672227159/5000000000 : ℝ)|^2101 ≤ (21837337951519/50000000000000 : ℝ)^1589
        have hw : |(2672227159/5000000000 : ℝ)|=(2672227159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266825081/10000000000 : ℝ)|^2101 ≤ (4283785419257/10000000000000 : ℝ)^1589
        have hw : |(5266825081/10000000000 : ℝ)|=(5266825081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219766127/1000000000 : ℝ)|^2101 ≤ (6743734941487/50000000000000 : ℝ)^1589
        have hw : |(-219766127/1000000000 : ℝ)|=(219766127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s8_3 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4252973/9765625 : ℝ)*x 0 + (2115447219/5000000000 : ℝ)*x 1 + (17931041/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252973/9765625 : ℝ)^2101 ≤ (16658676652197/50000000000000 : ℝ)^1589 := by
    have hnat : (4252973 : ℕ)^2101*50000000000000^1589 ≤ 16658676652197^1589*9765625^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252973 9765625 16658676652197 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115447219/5000000000 : ℝ)^2101 ≤ (32067341136167/100000000000000 : ℝ)^1589 := by
    have hnat : (2115447219 : ℕ)^2101*100000000000000^1589 ≤ 32067341136167^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115447219 5000000000 32067341136167 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17931041/40000000 : ℝ)^2101 ≤ (17307652773293/50000000000000 : ℝ)^1589 := by
    have hnat : (17931041 : ℕ)^2101*50000000000000^1589 ≤ 17307652773293^1589*40000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17931041 40000000 17307652773293 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252973/9765625 : ℝ), (2115447219/5000000000 : ℝ), (17931041/40000000 : ℝ)] ![(16658676652197/50000000000000 : ℝ), (32067341136167/100000000000000 : ℝ), (17307652773293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252973/9765625 : ℝ)|^2101 ≤ (16658676652197/50000000000000 : ℝ)^1589
        have hw : |(4252973/9765625 : ℝ)|=(4252973/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115447219/5000000000 : ℝ)|^2101 ≤ (32067341136167/100000000000000 : ℝ)^1589
        have hw : |(2115447219/5000000000 : ℝ)|=(2115447219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17931041/40000000 : ℝ)|^2101 ≤ (17307652773293/50000000000000 : ℝ)^1589
        have hw : |(17931041/40000000 : ℝ)|=(17931041/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s8_4 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-533582099/2500000000 : ℝ)*x 0 + (5267140207/10000000000 : ℝ)*x 1 + (5391415407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533582099/2500000000 : ℝ)^2101 ≤ (12975945106209/100000000000000 : ℝ)^1589 := by
    have hnat : (533582099 : ℕ)^2101*100000000000000^1589 ≤ 12975945106209^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533582099 2500000000 12975945106209 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267140207/10000000000 : ℝ)^2101 ≤ (2142062158779/5000000000000 : ℝ)^1589 := by
    have hnat : (5267140207 : ℕ)^2101*5000000000000^1589 ≤ 2142062158779^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267140207 10000000000 2142062158779 5000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391415407/10000000000 : ℝ)^2101 ≤ (5522851462207/12500000000000 : ℝ)^1589 := by
    have hnat : (5391415407 : ℕ)^2101*12500000000000^1589 ≤ 5522851462207^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391415407 10000000000 5522851462207 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533582099/2500000000 : ℝ), (5267140207/10000000000 : ℝ), (5391415407/10000000000 : ℝ)] ![(12975945106209/100000000000000 : ℝ), (2142062158779/5000000000000 : ℝ), (5522851462207/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533582099/2500000000 : ℝ)|^2101 ≤ (12975945106209/100000000000000 : ℝ)^1589
        have hw : |(-533582099/2500000000 : ℝ)|=(533582099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267140207/10000000000 : ℝ)|^2101 ≤ (2142062158779/5000000000000 : ℝ)^1589
        have hw : |(5267140207/10000000000 : ℝ)|=(5267140207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391415407/10000000000 : ℝ)|^2101 ≤ (5522851462207/12500000000000 : ℝ)^1589
        have hw : |(5391415407/10000000000 : ℝ)|=(5391415407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s8_5 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062530179/2000000000 : ℝ)*x 0 + (-1036535103/5000000000 : ℝ)*x 1 + (5391416687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062530179/2000000000 : ℝ)^2101 ≤ (43331366879021/100000000000000 : ℝ)^1589 := by
    have hnat : (1062530179 : ℕ)^2101*100000000000000^1589 ≤ 43331366879021^1589*2000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062530179 2000000000 43331366879021 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036535103/5000000000 : ℝ)^2101 ≤ (1248580754003/10000000000000 : ℝ)^1589 := by
    have hnat : (1036535103 : ℕ)^2101*10000000000000^1589 ≤ 1248580754003^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036535103 5000000000 1248580754003 10000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391416687/10000000000 : ℝ)^2101 ≤ (2761426597951/6250000000000 : ℝ)^1589 := by
    have hnat : (5391416687 : ℕ)^2101*6250000000000^1589 ≤ 2761426597951^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391416687 10000000000 2761426597951 6250000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062530179/2000000000 : ℝ), (-1036535103/5000000000 : ℝ), (5391416687/10000000000 : ℝ)] ![(43331366879021/100000000000000 : ℝ), (1248580754003/10000000000000 : ℝ), (2761426597951/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062530179/2000000000 : ℝ)|^2101 ≤ (43331366879021/100000000000000 : ℝ)^1589
        have hw : |(1062530179/2000000000 : ℝ)|=(1062530179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036535103/5000000000 : ℝ)|^2101 ≤ (1248580754003/10000000000000 : ℝ)^1589
        have hw : |(-1036535103/5000000000 : ℝ)|=(1036535103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391416687/10000000000 : ℝ)|^2101 ≤ (2761426597951/6250000000000 : ℝ)^1589
        have hw : |(5391416687/10000000000 : ℝ)|=(5391416687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s8_6 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1328162901/2500000000 : ℝ)*x 0 + (2695707889/5000000000 : ℝ)*x 1 + (-1036535241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328162901/2500000000 : ℝ)^2101 ≤ (5416421815639/12500000000000 : ℝ)^1589 := by
    have hnat : (1328162901 : ℕ)^2101*12500000000000^1589 ≤ 5416421815639^1589*2500000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328162901 2500000000 5416421815639 12500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695707889/5000000000 : ℝ)^2101 ≤ (44182815717661/100000000000000 : ℝ)^1589 := by
    have hnat : (2695707889 : ℕ)^2101*100000000000000^1589 ≤ 44182815717661^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695707889 5000000000 44182815717661 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036535241/5000000000 : ℝ)^2101 ≤ (312145243449/2500000000000 : ℝ)^1589 := by
    have hnat : (1036535241 : ℕ)^2101*2500000000000^1589 ≤ 312145243449^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036535241 5000000000 312145243449 2500000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328162901/2500000000 : ℝ), (2695707889/5000000000 : ℝ), (-1036535241/5000000000 : ℝ)] ![(5416421815639/12500000000000 : ℝ), (44182815717661/100000000000000 : ℝ), (312145243449/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328162901/2500000000 : ℝ)|^2101 ≤ (5416421815639/12500000000000 : ℝ)^1589
        have hw : |(1328162901/2500000000 : ℝ)|=(1328162901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695707889/5000000000 : ℝ)|^2101 ≤ (44182815717661/100000000000000 : ℝ)^1589
        have hw : |(2695707889/5000000000 : ℝ)|=(2695707889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1036535241/5000000000 : ℝ)|^2101 ≤ (312145243449/2500000000000 : ℝ)^1589
        have hw : |(-1036535241/5000000000 : ℝ)|=(1036535241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1211_s8_7 (p : ℝ) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4355053633/10000000000 : ℝ)*x 0 + (4482126609/10000000000 : ℝ)*x 1 + (2115765299/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355053633/10000000000 : ℝ)^2101 ≤ (16658723592403/50000000000000 : ℝ)^1589 := by
    have hnat : (4355053633 : ℕ)^2101*50000000000000^1589 ≤ 16658723592403^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355053633 10000000000 16658723592403 50000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4482126609/10000000000 : ℝ)^2101 ≤ (8652209058289/25000000000000 : ℝ)^1589 := by
    have hnat : (4482126609 : ℕ)^2101*25000000000000^1589 ≤ 8652209058289^1589*10000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482126609 10000000000 8652209058289 25000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115765299/5000000000 : ℝ)^2101 ≤ (32073716570777/100000000000000 : ℝ)^1589 := by
    have hnat : (2115765299 : ℕ)^2101*100000000000000^1589 ≤ 32073716570777^1589*5000000000^2101 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115765299 5000000000 32073716570777 100000000000000 2101 1589 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2101/512 : ℝ)) 2101 1589 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355053633/10000000000 : ℝ), (4482126609/10000000000 : ℝ), (2115765299/5000000000 : ℝ)] ![(16658723592403/50000000000000 : ℝ), (8652209058289/25000000000000 : ℝ), (32073716570777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355053633/10000000000 : ℝ)|^2101 ≤ (16658723592403/50000000000000 : ℝ)^1589
        have hw : |(4355053633/10000000000 : ℝ)|=(4355053633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4482126609/10000000000 : ℝ)|^2101 ≤ (8652209058289/25000000000000 : ℝ)^1589
        have hw : |(4482126609/10000000000 : ℝ)|=(4482126609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115765299/5000000000 : ℝ)|^2101 ≤ (32073716570777/100000000000000 : ℝ)^1589
        have hw : |(2115765299/5000000000 : ℝ)|=(2115765299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1211_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (11441/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14087/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (143/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (143/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (143/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1761/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (143/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (143/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1761/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (143/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (143/1250 : ℝ) ^ (8403/2048 : ℝ) ≤ (2739846472934977/20000000000000000000 : ℝ) := by
    have hpowers : (143/1250 : ℝ)^8403 ≤ (2739846472934977/20000000000000000000 : ℝ)^2048 := by
      have hnat : (143 : ℕ)^8403*20000000000000000000^2048 ≤ 2739846472934977^2048*1250^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        143 1250 2739846472934977 20000000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (143/1250 : ℝ)) (X := (2739846472934977/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1761/12500 : ℝ) ^ (8403/2048 : ℝ) ≤ (4023607356557627/12500000000000000000 : ℝ) := by
    have hpowers : (1761/12500 : ℝ)^8403 ≤ (4023607356557627/12500000000000000000 : ℝ)^2048 := by
      have hnat : (1761 : ℕ)^8403*12500000000000000000^2048 ≤ 4023607356557627^2048*12500^8403 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1761 12500 4023607356557627 12500000000000000000 8403 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1761/12500 : ℝ)) (X := (4023607356557627/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002739846472934977/10000000000000000000 : ℝ) ≤ (2000133538601101/2000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (10002739846472934977/10000000000000000000 : ℝ)^2048 ≤ (2000133538601101/2000000000000000 : ℝ)^8403 := by
      have hnat : (10002739846472934977 : ℕ)^2048*2000000000000000^8403 ≤ 2000133538601101^8403*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002739846472934977 10000000000000000000 2000133538601101 2000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000133538601101/2000000000000000 : ℝ)) (X := (10002739846472934977/10000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045888091217135901/100000000000000000000 : ℝ) ≤ (5000559100963507/5000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (100045888091217135901/100000000000000000000 : ℝ)^2048 ≤ (5000559100963507/5000000000000000 : ℝ)^8403 := by
      have hnat : (100045888091217135901 : ℕ)^2048*5000000000000000^8403 ≤ 5000559100963507^8403*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045888091217135901 100000000000000000000 5000559100963507 5000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000559100963507/5000000000000000 : ℝ)) (X := (100045888091217135901/100000000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254023607356557627/6250000000000000000 : ℝ) ≤ (10001568710848523/10000000000000000 : ℝ) ^ (8403/2048 : ℝ) := by
    have hpowers : (6254023607356557627/6250000000000000000 : ℝ)^2048 ≤ (10001568710848523/10000000000000000 : ℝ)^8403 := by
      have hnat : (6254023607356557627 : ℕ)^2048*10000000000000000^8403 ≤ 10001568710848523^8403*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254023607356557627 6250000000000000000 10001568710848523 10000000000000000 2048 8403 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001568710848523/10000000000000000 : ℝ)) (X := (6254023607356557627/6250000000000000000 : ℝ)) (by norm_num) 8403 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2739846472934977/20000000000000000000 : ℝ) ≤ ((661786510173861283/662000000000000000 : ℝ)+2*(450508921509/264800000000000 : ℝ)*(143/1250 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (661786510173861283/662000000000000000 : ℝ)+2*(450508921509/264800000000000 : ℝ)*(143/1250 : ℝ)=(2000133538601101/2000000000000000 : ℝ) by norm_num, show 1+2*(2739846472934977/20000000000000000000 : ℝ)=(10002739846472934977/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4023607356557627/12500000000000000000 : ℝ)+(2739846472934977/20000000000000000000 : ℝ) ≤ ((661786510173861283/662000000000000000 : ℝ)+(450508921509/264800000000000 : ℝ)*((1761/12500 : ℝ)+(143/1250 : ℝ)))^(8403/2048 : ℝ) := by
    rw [show (661786510173861283/662000000000000000 : ℝ)+(450508921509/264800000000000 : ℝ)*((1761/12500 : ℝ)+(143/1250 : ℝ))=(5000559100963507/5000000000000000 : ℝ) by norm_num, show 1+(4023607356557627/12500000000000000000 : ℝ)+(2739846472934977/20000000000000000000 : ℝ)=(100045888091217135901/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4023607356557627/12500000000000000000 : ℝ) ≤ ((661786510173861283/662000000000000000 : ℝ)+2*(450508921509/264800000000000 : ℝ)*(1761/12500 : ℝ))^(8403/2048 : ℝ) := by
    rw [show (661786510173861283/662000000000000000 : ℝ)+2*(450508921509/264800000000000 : ℝ)*(1761/12500 : ℝ)=(10001568710848523/10000000000000000 : ℝ) by norm_num, show 1+2*(4023607356557627/12500000000000000000 : ℝ)=(6254023607356557627/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (661786510173861283/662000000000000000 : ℝ)*(X 1 0+X 2 0)+(450508921509/264800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (661786510173861283/662000000000000000 : ℝ)) (alpha := (450508921509/264800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (661786510173861283/662000000000000000 : ℝ)*(X 0 1+X 2 1)+(450508921509/264800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (661786510173861283/662000000000000000 : ℝ)) (alpha := (450508921509/264800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (661786510173861283/662000000000000000 : ℝ)*(X 0 2+X 1 2)+(450508921509/264800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8403/2048 : ℝ)) (lo := (143/1250 : ℝ)) (hi := (1761/12500 : ℝ)) (c := (661786510173861283/662000000000000000 : ℝ)) (alpha := (450508921509/264800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2134323799/10000000000 : ℝ)*X 0 0+(5391731577/10000000000 : ℝ)*X 0 1+(5266825083/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336113579/2500000000 : ℝ)*X 1 0+(-2197661279/10000000000 : ℝ)*X 1 1+(1316706269/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672227159/5000000000 : ℝ)*X 2 0+(5266825081/10000000000 : ℝ)*X 2 1+(-219766127/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4252973/9765625 : ℝ)*X 0 0+(2115447219/5000000000 : ℝ)*X 0 1+(17931041/40000000 : ℝ)*X 0 2+(4252973/9765625 : ℝ)*X 1 0+(2115447219/5000000000 : ℝ)*X 1 1+(17931041/40000000 : ℝ)*X 1 2+(4252973/9765625 : ℝ)*X 2 0+(2115447219/5000000000 : ℝ)*X 2 1+(17931041/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-533582099/2500000000 : ℝ)*X 0 0+(5267140207/10000000000 : ℝ)*X 0 1+(5391415407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062530179/2000000000 : ℝ)*X 1 0+(-1036535103/5000000000 : ℝ)*X 1 1+(5391416687/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328162901/2500000000 : ℝ)*X 2 0+(2695707889/5000000000 : ℝ)*X 2 1+(-1036535241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355053633/10000000000 : ℝ)*X 0 0+(4482126609/10000000000 : ℝ)*X 0 1+(2115765299/5000000000 : ℝ)*X 0 2+(4355053633/10000000000 : ℝ)*X 1 0+(4482126609/10000000000 : ℝ)*X 1 1+(2115765299/5000000000 : ℝ)*X 1 2+(4355053633/10000000000 : ℝ)*X 2 0+(4482126609/10000000000 : ℝ)*X 2 1+(2115765299/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1211_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7570481746508867856261/827500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1771668121/100000000000000 : ℝ)*(base19) + (1652564919/100000000000000 : ℝ)*(base23) + (65255381/100000000000000 : ℝ)*(lower2) + (219250159/100000000000000 : ℝ)*(upper3) + (144901127/100000000000000 : ℝ)*(upper5) + (187132920093237/3125000000000 : ℝ)*(major0) + (187132920093237/3125000000000 : ℝ)*(major1) + (187132920093237/3125000000000 : ℝ)*(major2) + (8006039632599001/100000000000000 : ℝ)*(sp0) + (4003043559468329/50000000000000 : ℝ)*(sp1) + (8006087238039861/100000000000000 : ℝ)*(sp2) + (1985195879671417/50000000000000 : ℝ)*(sp3) + (24629002889/50000000000000 : ℝ)*(sp4) + (25931065601/100000000000000 : ℝ)*(sp7) + (794083538081687/20000000000000 : ℝ)*(f.failure) + (8006088890604779/100000000000000 : ℝ)*(f.sum) + (2836935612431/827500000000000000000000000 : ℝ)*base65 + (5738601439500571/2068750000000000000000000000000 : ℝ)*base67 + (2348402822669321/2068750000000000000000000000000 : ℝ)*base69 + (10539902027093179/2068750000000000000000000000000 : ℝ)*base72 + (4568639708587/1655000000000000000000000000 : ℝ)*base73 + (23010897954511929/2068750000000000000000000000000 : ℝ)*base76 + (6426219029344321/2068750000000000000000000000000 : ℝ)*base77 + (25251445510861929/2068750000000000000000000000000 : ℝ)*base80 + (431774156887/103437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (14831/8000000000000000000 : ℝ)*base90 + (14831/8000000000000000000 : ℝ)*base92 + (14831/8000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37290750435536841150051/6620000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21268953/50000000000000 : ℝ)*(base15) + (543989637/100000000000000 : ℝ)*(lower1) + (24333217/10000000000000 : ℝ)*(lower2) + (2327517/6250000000000 : ℝ)*(upper3) + (99271773/50000000000000 : ℝ)*(upper4) + (3009289680449493/50000000000000 : ℝ)*(major0) + (3009289680449493/50000000000000 : ℝ)*(major1) + (3009289680449493/50000000000000 : ℝ)*(major2) + (136704309/400000000000 : ℝ)*(sp1) + (25313508417/100000000000000 : ℝ)*(sp3) + (804663371854467/10000000000000 : ℝ)*(sp4) + (1609319899985903/20000000000000 : ℝ)*(sp5) + (804663371854467/10000000000000 : ℝ)*(sp6) + (199524975098837/5000000000000 : ℝ)*(sp7) + (1995262407742579/50000000000000 : ℝ)*(f.failure) + (804663371854467/10000000000000 : ℝ)*(f.sum) + (1928453347143/6620000000000000000000000000 : ℝ)*base66 + (328772430014422019/33100000000000000000000000000000 : ℝ)*base67 + (1062742946243977981/33100000000000000000000000000000 : ℝ)*base70 + (1271509236187877981/33100000000000000000000000000000 : ℝ)*base72 + (43637876640017/6620000000000000000000000000 : ℝ)*base73 + (289931001750477981/33100000000000000000000000000000 : ℝ)*base76 + (297180072521622019/33100000000000000000000000000000 : ℝ)*base77 + (588499637547422019/33100000000000000000000000000000 : ℝ)*base79 + (23003395109663/6620000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (57173/20000000000000000000 : ℝ)*base89 + (57173/20000000000000000000 : ℝ)*base91 + (57173/20000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1211_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1761/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (143/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1211_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1211_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1211_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1211_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1211_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8403/2048 : ℝ) ≤ p) (hpb : p ≤ (2101/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (603287/400000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14117/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11413/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11441/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14087/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1211_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
