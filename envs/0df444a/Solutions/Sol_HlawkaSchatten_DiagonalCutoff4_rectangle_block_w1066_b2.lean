-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:07:16.706482+00:00
-- url     : https://prove2.me/submissions/f06bcd3a-5f36-4b24-a392-51262813e881

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
theorem support_rectangle_w1066_s6_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203722077/10000000000 : ℝ)*x 0 + (1078983347/2000000000 : ℝ)*x 1 + (2631961651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203722077/10000000000 : ℝ)^8259 ≤ (418235579717/3125000000000 : ℝ)^6211 := by
    have hnat : (2203722077 : ℕ)^8259*3125000000000^6211 ≤ 418235579717^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203722077 10000000000 418235579717 3125000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078983347/2000000000 : ℝ)^8259 ≤ (44015946959049/100000000000000 : ℝ)^6211 := by
    have hnat : (1078983347 : ℕ)^8259*100000000000000^6211 ≤ 44015946959049^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078983347 2000000000 44015946959049 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631961651/5000000000 : ℝ)^8259 ≤ (10650128619693/25000000000000 : ℝ)^6211 := by
    have hnat : (2631961651 : ℕ)^8259*25000000000000^6211 ≤ 10650128619693^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631961651 5000000000 10650128619693 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203722077/10000000000 : ℝ), (1078983347/2000000000 : ℝ), (2631961651/5000000000 : ℝ)] ![(418235579717/3125000000000 : ℝ), (44015946959049/100000000000000 : ℝ), (10650128619693/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203722077/10000000000 : ℝ)|^8259 ≤ (418235579717/3125000000000 : ℝ)^6211
        have hw : |(-2203722077/10000000000 : ℝ)|=(2203722077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078983347/2000000000 : ℝ)|^8259 ≤ (44015946959049/100000000000000 : ℝ)^6211
        have hw : |(1078983347/2000000000 : ℝ)|=(1078983347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631961651/5000000000 : ℝ)|^8259 ≤ (10650128619693/25000000000000 : ℝ)^6211
        have hw : |(2631961651/5000000000 : ℝ)|=(2631961651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s6_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672559133/5000000000 : ℝ)*x 0 + (-454038357/2000000000 : ℝ)*x 1 + (5263923367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672559133/5000000000 : ℝ)^8259 ≤ (21738252682591/50000000000000 : ℝ)^6211 := by
    have hnat : (2672559133 : ℕ)^8259*50000000000000^6211 ≤ 21738252682591^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672559133 5000000000 21738252682591 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454038357/2000000000 : ℝ)^8259 ≤ (3480744861163/25000000000000 : ℝ)^6211 := by
    have hnat : (454038357 : ℕ)^8259*25000000000000^6211 ≤ 3480744861163^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454038357 2000000000 3480744861163 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263923367/10000000000 : ℝ)^8259 ≤ (42600515178267/100000000000000 : ℝ)^6211 := by
    have hnat : (5263923367 : ℕ)^8259*100000000000000^6211 ≤ 42600515178267^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263923367 10000000000 42600515178267 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672559133/5000000000 : ℝ), (-454038357/2000000000 : ℝ), (5263923367/10000000000 : ℝ)] ![(21738252682591/50000000000000 : ℝ), (3480744861163/25000000000000 : ℝ), (42600515178267/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672559133/5000000000 : ℝ)|^8259 ≤ (21738252682591/50000000000000 : ℝ)^6211
        have hw : |(2672559133/5000000000 : ℝ)|=(2672559133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454038357/2000000000 : ℝ)|^8259 ≤ (3480744861163/25000000000000 : ℝ)^6211
        have hw : |(-454038357/2000000000 : ℝ)|=(454038357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263923367/10000000000 : ℝ)|^8259 ≤ (42600515178267/100000000000000 : ℝ)^6211
        have hw : |(5263923367/10000000000 : ℝ)|=(5263923367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s6_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672558919/5000000000 : ℝ)*x 0 + (5263923621/10000000000 : ℝ)*x 1 + (-2270192017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672558919/5000000000 : ℝ)^8259 ≤ (43476500735971/100000000000000 : ℝ)^6211 := by
    have hnat : (2672558919 : ℕ)^8259*100000000000000^6211 ≤ 43476500735971^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672558919 5000000000 43476500735971 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263923621/10000000000 : ℝ)^8259 ≤ (21300258955839/50000000000000 : ℝ)^6211 := by
    have hnat : (5263923621 : ℕ)^8259*50000000000000^6211 ≤ 21300258955839^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263923621 10000000000 21300258955839 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270192017/10000000000 : ℝ)^8259 ≤ (6961490668331/50000000000000 : ℝ)^6211 := by
    have hnat : (2270192017 : ℕ)^8259*50000000000000^6211 ≤ 6961490668331^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270192017 10000000000 6961490668331 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672558919/5000000000 : ℝ), (5263923621/10000000000 : ℝ), (-2270192017/10000000000 : ℝ)] ![(43476500735971/100000000000000 : ℝ), (21300258955839/50000000000000 : ℝ), (6961490668331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672558919/5000000000 : ℝ)|^8259 ≤ (43476500735971/100000000000000 : ℝ)^6211
        have hw : |(2672558919/5000000000 : ℝ)|=(2672558919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263923621/10000000000 : ℝ)|^8259 ≤ (21300258955839/50000000000000 : ℝ)^6211
        have hw : |(5263923621/10000000000 : ℝ)|=(5263923621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2270192017/10000000000 : ℝ)|^8259 ≤ (6961490668331/50000000000000 : ℝ)^6211
        have hw : |(-2270192017/10000000000 : ℝ)|=(2270192017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s6_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187732171/5000000000 : ℝ)*x 0 + (1062251827/2500000000 : ℝ)*x 1 + (450573643/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187732171/5000000000 : ℝ)^8259 ≤ (4164533306781/12500000000000 : ℝ)^6211 := by
    have hnat : (2187732171 : ℕ)^8259*12500000000000^6211 ≤ 4164533306781^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187732171 5000000000 4164533306781 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062251827/2500000000 : ℝ)^8259 ≤ (8010505184187/25000000000000 : ℝ)^6211 := by
    have hnat : (1062251827 : ℕ)^8259*25000000000000^6211 ≤ 8010505184187^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062251827 2500000000 8010505184187 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450573643/1000000000 : ℝ)^8259 ≤ (6928342559821/20000000000000 : ℝ)^6211 := by
    have hnat : (450573643 : ℕ)^8259*20000000000000^6211 ≤ 6928342559821^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450573643 1000000000 6928342559821 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187732171/5000000000 : ℝ), (1062251827/2500000000 : ℝ), (450573643/1000000000 : ℝ)] ![(4164533306781/12500000000000 : ℝ), (8010505184187/25000000000000 : ℝ), (6928342559821/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187732171/5000000000 : ℝ)|^8259 ≤ (4164533306781/12500000000000 : ℝ)^6211
        have hw : |(2187732171/5000000000 : ℝ)|=(2187732171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062251827/2500000000 : ℝ)|^8259 ≤ (8010505184187/25000000000000 : ℝ)^6211
        have hw : |(1062251827/2500000000 : ℝ)|=(1062251827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450573643/1000000000 : ℝ)|^8259 ≤ (6928342559821/20000000000000 : ℝ)^6211
        have hw : |(450573643/1000000000 : ℝ)|=(450573643/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s6_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101863641/5000000000 : ℝ)*x 0 + (658031783/1250000000 : ℝ)*x 1 + (5394584563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101863641/5000000000 : ℝ)^8259 ≤ (1672947573121/12500000000000 : ℝ)^6211 := by
    have hnat : (1101863641 : ℕ)^8259*12500000000000^6211 ≤ 1672947573121^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101863641 5000000000 1672947573121 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658031783/1250000000 : ℝ)^8259 ≤ (42604076150281/100000000000000 : ℝ)^6211 := by
    have hnat : (658031783 : ℕ)^8259*100000000000000^6211 ≤ 42604076150281^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658031783 1250000000 42604076150281 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394584563/10000000000 : ℝ)^8259 ≤ (22006171624449/50000000000000 : ℝ)^6211 := by
    have hnat : (5394584563 : ℕ)^8259*50000000000000^6211 ≤ 22006171624449^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394584563 10000000000 22006171624449 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101863641/5000000000 : ℝ), (658031783/1250000000 : ℝ), (5394584563/10000000000 : ℝ)] ![(1672947573121/12500000000000 : ℝ), (42604076150281/100000000000000 : ℝ), (22006171624449/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101863641/5000000000 : ℝ)|^8259 ≤ (1672947573121/12500000000000 : ℝ)^6211
        have hw : |(-1101863641/5000000000 : ℝ)|=(1101863641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658031783/1250000000 : ℝ)|^8259 ≤ (42604076150281/100000000000000 : ℝ)^6211
        have hw : |(658031783/1250000000 : ℝ)|=(658031783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394584563/10000000000 : ℝ)|^8259 ≤ (22006171624449/50000000000000 : ℝ)^6211
        have hw : |(5394584563/10000000000 : ℝ)|=(5394584563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s6_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656061821/5000000000 : ℝ)*x 0 + (-1069765327/5000000000 : ℝ)*x 1 + (1078916927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656061821/5000000000 : ℝ)^8259 ≤ (43120002021911/100000000000000 : ℝ)^6211 := by
    have hnat : (2656061821 : ℕ)^8259*100000000000000^6211 ≤ 43120002021911^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656061821 5000000000 43120002021911 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069765327/5000000000 : ℝ)^8259 ≤ (12867653927987/100000000000000 : ℝ)^6211 := by
    have hnat : (1069765327 : ℕ)^8259*100000000000000^6211 ≤ 12867653927987^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069765327 5000000000 12867653927987 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078916927/2000000000 : ℝ)^8259 ≤ (44012344030013/100000000000000 : ℝ)^6211 := by
    have hnat : (1078916927 : ℕ)^8259*100000000000000^6211 ≤ 44012344030013^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078916927 2000000000 44012344030013 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656061821/5000000000 : ℝ), (-1069765327/5000000000 : ℝ), (1078916927/2000000000 : ℝ)] ![(43120002021911/100000000000000 : ℝ), (12867653927987/100000000000000 : ℝ), (44012344030013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656061821/5000000000 : ℝ)|^8259 ≤ (43120002021911/100000000000000 : ℝ)^6211
        have hw : |(2656061821/5000000000 : ℝ)|=(2656061821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069765327/5000000000 : ℝ)|^8259 ≤ (12867653927987/100000000000000 : ℝ)^6211
        have hw : |(-1069765327/5000000000 : ℝ)|=(1069765327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078916927/2000000000 : ℝ)|^8259 ≤ (44012344030013/100000000000000 : ℝ)^6211
        have hw : |(1078916927/2000000000 : ℝ)|=(1078916927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s6_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328030839/2500000000 : ℝ)*x 0 + (5394584999/10000000000 : ℝ)*x 1 + (-2139530547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328030839/2500000000 : ℝ)^8259 ≤ (43119998934869/100000000000000 : ℝ)^6211 := by
    have hnat : (1328030839 : ℕ)^8259*100000000000000^6211 ≤ 43119998934869^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328030839 2500000000 43119998934869 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394584999/10000000000 : ℝ)^8259 ≤ (44012347978983/100000000000000 : ℝ)^6211 := by
    have hnat : (5394584999 : ℕ)^8259*100000000000000^6211 ≤ 44012347978983^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394584999 10000000000 44012347978983 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2139530547/10000000000 : ℝ)^8259 ≤ (12867653072269/100000000000000 : ℝ)^6211 := by
    have hnat : (2139530547 : ℕ)^8259*100000000000000^6211 ≤ 12867653072269^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2139530547 10000000000 12867653072269 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328030839/2500000000 : ℝ), (5394584999/10000000000 : ℝ), (-2139530547/10000000000 : ℝ)] ![(43119998934869/100000000000000 : ℝ), (44012347978983/100000000000000 : ℝ), (12867653072269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328030839/2500000000 : ℝ)|^8259 ≤ (43119998934869/100000000000000 : ℝ)^6211
        have hw : |(1328030839/2500000000 : ℝ)|=(1328030839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394584999/10000000000 : ℝ)|^8259 ≤ (44012347978983/100000000000000 : ℝ)^6211
        have hw : |(5394584999/10000000000 : ℝ)|=(5394584999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2139530547/10000000000 : ℝ)|^8259 ≤ (12867653072269/100000000000000 : ℝ)^6211
        have hw : |(-2139530547/10000000000 : ℝ)|=(2139530547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s6_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375474547/10000000000 : ℝ)*x 0 + (4505087833/10000000000 : ℝ)*x 1 + (4249658237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375474547/10000000000 : ℝ)^8259 ≤ (16658184890323/50000000000000 : ℝ)^6211 := by
    have hnat : (4375474547 : ℕ)^8259*50000000000000^6211 ≤ 16658184890323^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375474547 10000000000 16658184890323 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4505087833/10000000000 : ℝ)^8259 ≤ (34635082026441/100000000000000 : ℝ)^6211 := by
    have hnat : (4505087833 : ℕ)^8259*100000000000000^6211 ≤ 34635082026441^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505087833 10000000000 34635082026441 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249658237/10000000000 : ℝ)^8259 ≤ (32048548177597/100000000000000 : ℝ)^6211 := by
    have hnat : (4249658237 : ℕ)^8259*100000000000000^6211 ≤ 32048548177597^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249658237 10000000000 32048548177597 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375474547/10000000000 : ℝ), (4505087833/10000000000 : ℝ), (4249658237/10000000000 : ℝ)] ![(16658184890323/50000000000000 : ℝ), (34635082026441/100000000000000 : ℝ), (32048548177597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375474547/10000000000 : ℝ)|^8259 ≤ (16658184890323/50000000000000 : ℝ)^6211
        have hw : |(4375474547/10000000000 : ℝ)|=(4375474547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4505087833/10000000000 : ℝ)|^8259 ≤ (34635082026441/100000000000000 : ℝ)^6211
        have hw : |(4505087833/10000000000 : ℝ)|=(4505087833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249658237/10000000000 : ℝ)|^8259 ≤ (32048548177597/100000000000000 : ℝ)^6211
        have hw : |(4249658237/10000000000 : ℝ)|=(4249658237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (281/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2803/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5599/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5599/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5599/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5599/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5599/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5599/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5599/50000 : ℝ) ^ (4129/1024 : ℝ) ≤ (915796407814511/6250000000000000000 : ℝ) := by
    have hpowers : (5599/50000 : ℝ)^4129 ≤ (915796407814511/6250000000000000000 : ℝ)^1024 := by
      have hnat : (5599 : ℕ)^4129*6250000000000000000^1024 ≤ 915796407814511^1024*50000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5599 50000 915796407814511 6250000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5599/50000 : ℝ)) (X := (915796407814511/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7029/50000 : ℝ) ^ (4129/1024 : ℝ) ≤ (36663562389449443/100000000000000000000 : ℝ) := by
    have hpowers : (7029/50000 : ℝ)^4129 ≤ (36663562389449443/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7029 : ℕ)^4129*100000000000000000000^1024 ≤ 36663562389449443^1024*50000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 50000 36663562389449443 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/50000 : ℝ)) (X := (36663562389449443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125915796407814511/3125000000000000000 : ℝ) ≤ (10000726701638057/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (3125915796407814511/3125000000000000000 : ℝ)^1024 ≤ (10000726701638057/10000000000000000 : ℝ)^4129 := by
      have hnat : (3125915796407814511 : ℕ)^1024*10000000000000000^4129 ≤ 10000726701638057^4129*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125915796407814511 3125000000000000000 10000726701638057 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000726701638057/10000000000000000 : ℝ)) (X := (3125915796407814511/3125000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051316304914481619/100000000000000000000 : ℝ) ≤ (10001272408820923/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (100051316304914481619/100000000000000000000 : ℝ)^1024 ≤ (10001272408820923/10000000000000000 : ℝ)^4129 := by
      have hnat : (100051316304914481619 : ℕ)^1024*10000000000000000^4129 ≤ 10001272408820923^4129*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051316304914481619 100000000000000000000 10001272408820923 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001272408820923/10000000000000000 : ℝ)) (X := (100051316304914481619/100000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036663562389449443/50000000000000000000 : ℝ) ≤ (10001818116003789/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50036663562389449443/50000000000000000000 : ℝ)^1024 ≤ (10001818116003789/10000000000000000 : ℝ)^4129 := by
      have hnat : (50036663562389449443 : ℕ)^1024*10000000000000000^4129 ≤ 10001818116003789^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036663562389449443 50000000000000000000 10001818116003789 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001818116003789/10000000000000000 : ℝ)) (X := (50036663562389449443/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(915796407814511/6250000000000000000 : ℝ) ≤ ((649769470650394911/650000000000000000 : ℝ)+2*(272853591433/143000000000000 : ℝ)*(5599/50000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (649769470650394911/650000000000000000 : ℝ)+2*(272853591433/143000000000000 : ℝ)*(5599/50000 : ℝ)=(10000726701638057/10000000000000000 : ℝ) by norm_num, show 1+2*(915796407814511/6250000000000000000 : ℝ)=(3125915796407814511/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36663562389449443/100000000000000000000 : ℝ)+(915796407814511/6250000000000000000 : ℝ) ≤ ((649769470650394911/650000000000000000 : ℝ)+(272853591433/143000000000000 : ℝ)*((7029/50000 : ℝ)+(5599/50000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (649769470650394911/650000000000000000 : ℝ)+(272853591433/143000000000000 : ℝ)*((7029/50000 : ℝ)+(5599/50000 : ℝ))=(10001272408820923/10000000000000000 : ℝ) by norm_num, show 1+(36663562389449443/100000000000000000000 : ℝ)+(915796407814511/6250000000000000000 : ℝ)=(100051316304914481619/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36663562389449443/100000000000000000000 : ℝ) ≤ ((649769470650394911/650000000000000000 : ℝ)+2*(272853591433/143000000000000 : ℝ)*(7029/50000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (649769470650394911/650000000000000000 : ℝ)+2*(272853591433/143000000000000 : ℝ)*(7029/50000 : ℝ)=(10001818116003789/10000000000000000 : ℝ) by norm_num, show 1+2*(36663562389449443/100000000000000000000 : ℝ)=(50036663562389449443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (649769470650394911/650000000000000000 : ℝ)*(X 1 0+X 2 0)+(272853591433/143000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (649769470650394911/650000000000000000 : ℝ)) (alpha := (272853591433/143000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (649769470650394911/650000000000000000 : ℝ)*(X 0 1+X 2 1)+(272853591433/143000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (649769470650394911/650000000000000000 : ℝ)) (alpha := (272853591433/143000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (649769470650394911/650000000000000000 : ℝ)*(X 0 2+X 1 2)+(272853591433/143000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (649769470650394911/650000000000000000 : ℝ)) (alpha := (272853591433/143000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2203722077/10000000000 : ℝ)*X 0 0+(1078983347/2000000000 : ℝ)*X 0 1+(2631961651/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672559133/5000000000 : ℝ)*X 1 0+(-454038357/2000000000 : ℝ)*X 1 1+(5263923367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672558919/5000000000 : ℝ)*X 2 0+(5263923621/10000000000 : ℝ)*X 2 1+(-2270192017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187732171/5000000000 : ℝ)*X 0 0+(1062251827/2500000000 : ℝ)*X 0 1+(450573643/1000000000 : ℝ)*X 0 2+(2187732171/5000000000 : ℝ)*X 1 0+(1062251827/2500000000 : ℝ)*X 1 1+(450573643/1000000000 : ℝ)*X 1 2+(2187732171/5000000000 : ℝ)*X 2 0+(1062251827/2500000000 : ℝ)*X 2 1+(450573643/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1101863641/5000000000 : ℝ)*X 0 0+(658031783/1250000000 : ℝ)*X 0 1+(5394584563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656061821/5000000000 : ℝ)*X 1 0+(-1069765327/5000000000 : ℝ)*X 1 1+(1078916927/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328030839/2500000000 : ℝ)*X 2 0+(5394584999/10000000000 : ℝ)*X 2 1+(-2139530547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375474547/10000000000 : ℝ)*X 0 0+(4505087833/10000000000 : ℝ)*X 0 1+(4249658237/10000000000 : ℝ)*X 0 2+(4375474547/10000000000 : ℝ)*X 1 0+(4505087833/10000000000 : ℝ)*X 1 1+(4249658237/10000000000 : ℝ)*X 1 2+(4375474547/10000000000 : ℝ)*X 2 0+(4505087833/10000000000 : ℝ)*X 2 1+(4249658237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (267771249448111831257401391/35750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1802889767/100000000000000 : ℝ)*(base19) + (1233241983/100000000000000 : ℝ)*(base23) + (27245117/100000000000000 : ℝ)*(upper2) + (201660107/50000000000000 : ℝ)*(upper3) + (1152928582197657/20000000000000 : ℝ)*(major0) + (1152928582197657/20000000000000 : ℝ)*(major1) + (1152928582197657/20000000000000 : ℝ)*(major2) + (7634035066091167/100000000000000 : ℝ)*(sp0) + (11928236785339/156250000000 : ℝ)*(sp1) + (3817035299898709/50000000000000 : ℝ)*(sp2) + (1947590901807909/50000000000000 : ℝ)*(sp3) + (956985389/2500000000000 : ℝ)*(sp4) + (60498693/4000000000000 : ℝ)*(sp6) + (15211591927/50000000000000 : ℝ)*(sp7) + (486901528349959/12500000000000 : ℝ)*(f.failure) + (7634073345506727/100000000000000 : ℝ)*(f.sum) + (2949715388031/1430000000000000000000000000 : ℝ)*base65 + (1305702371250791203/143000000000000000000000000000000 : ℝ)*base68 + (1085919227813791203/143000000000000000000000000000000 : ℝ)*base70 + (810342269299791203/143000000000000000000000000000000 : ℝ)*base72 + (2255380874301/1430000000000000000000000000 : ℝ)*base73 + (3575382004471791203/143000000000000000000000000000000 : ℝ)*base76 + (827515657531791203/143000000000000000000000000000000 : ℝ)*base78 + (652576713225208797/143000000000000000000000000000000 : ℝ)*base79 + (574425124971/1430000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1457279/625000000000000000000 : ℝ)*base90 + (1457279/625000000000000000000 : ℝ)*base92 + (1457279/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119547800914678668699921051/13750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (940821751/50000000000000 : ℝ)*(base19) + (1560155083/100000000000000 : ℝ)*(base23) + (17290639/100000000000000 : ℝ)*(upper2) + (74208333/25000000000000 : ℝ)*(upper3) + (173062943/100000000000000 : ℝ)*(upper5) + (5793888387358201/100000000000000 : ℝ)*(major0) + (5793888387358201/100000000000000 : ℝ)*(major1) + (5793888387358201/100000000000000 : ℝ)*(major2) + (23916262571/50000000000000 : ℝ)*(sp1) + (14335311679/25000000000000 : ℝ)*(sp2) + (479550179469429/6250000000000 : ℝ)*(sp4) + (383637657867111/5000000000000 : ℝ)*(sp5) + (1534548794021813/20000000000000 : ℝ)*(sp6) + (97874340334817/2500000000000 : ℝ)*(sp7) + (97874340334817/2500000000000 : ℝ)*(f.failure) + (479550179469429/6250000000000 : ℝ)*(f.sum) + (2776660226059/550000000000000000000000000 : ℝ)*base66 + (140699071640667983/55000000000000000000000000000000 : ℝ)*base68 + (152112179720667983/55000000000000000000000000000000 : ℝ)*base70 + (1119123685620667983/55000000000000000000000000000000 : ℝ)*base72 + (1410727496041/550000000000000000000000000 : ℝ)*base73 + (88986349269332017/55000000000000000000000000000000 : ℝ)*base75 + (940326008100667983/55000000000000000000000000000000 : ℝ)*base78 + (275430947765667983/55000000000000000000000000000000 : ℝ)*base80 + (3274546407391/550000000000000000000000000 : ℝ)*base81 + (1252023/125000000000000000000 : ℝ)*base89 + (1252023/125000000000000000000 : ℝ)*base91 + (1252023/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1066_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1066_s7_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-550939791/2500000000 : ℝ)*x 0 + (5394456661/10000000000 : ℝ)*x 1 + (1316089819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550939791/2500000000 : ℝ)^8259 ≤ (6691919027593/50000000000000 : ℝ)^6211 := by
    have hnat : (550939791 : ℕ)^8259*50000000000000^6211 ≤ 6691919027593^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550939791 2500000000 6691919027593 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394456661/10000000000 : ℝ)^8259 ≤ (11002738917201/25000000000000 : ℝ)^6211 := by
    have hnat : (5394456661 : ℕ)^8259*25000000000000^6211 ≤ 11002738917201^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394456661 10000000000 11002738917201 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316089819/2500000000 : ℝ)^8259 ≤ (42605206259947/100000000000000 : ℝ)^6211 := by
    have hnat : (1316089819 : ℕ)^8259*100000000000000^6211 ≤ 42605206259947^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316089819 2500000000 42605206259947 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550939791/2500000000 : ℝ), (5394456661/10000000000 : ℝ), (1316089819/2500000000 : ℝ)] ![(6691919027593/50000000000000 : ℝ), (11002738917201/25000000000000 : ℝ), (42605206259947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550939791/2500000000 : ℝ)|^8259 ≤ (6691919027593/50000000000000 : ℝ)^6211
        have hw : |(-550939791/2500000000 : ℝ)|=(550939791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394456661/10000000000 : ℝ)|^8259 ≤ (11002738917201/25000000000000 : ℝ)^6211
        have hw : |(5394456661/10000000000 : ℝ)|=(5394456661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316089819/2500000000 : ℝ)|^8259 ≤ (42605206259947/100000000000000 : ℝ)^6211
        have hw : |(1316089819/2500000000 : ℝ)|=(1316089819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s7_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1069000829/2000000000 : ℝ)*x 0 + (-1134883831/5000000000 : ℝ)*x 1 + (5264359457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069000829/2000000000 : ℝ)^8259 ≤ (21737635523273/50000000000000 : ℝ)^6211 := by
    have hnat : (1069000829 : ℕ)^8259*50000000000000^6211 ≤ 21737635523273^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069000829 2000000000 21737635523273 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134883831/5000000000 : ℝ)^8259 ≤ (6959760367849/50000000000000 : ℝ)^6211 := by
    have hnat : (1134883831 : ℕ)^8259*50000000000000^6211 ≤ 6959760367849^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134883831 5000000000 6959760367849 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264359457/10000000000 : ℝ)^8259 ≤ (1704208328313/4000000000000 : ℝ)^6211 := by
    have hnat : (5264359457 : ℕ)^8259*4000000000000^6211 ≤ 1704208328313^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264359457 10000000000 1704208328313 4000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069000829/2000000000 : ℝ), (-1134883831/5000000000 : ℝ), (5264359457/10000000000 : ℝ)] ![(21737635523273/50000000000000 : ℝ), (6959760367849/50000000000000 : ℝ), (1704208328313/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069000829/2000000000 : ℝ)|^8259 ≤ (21737635523273/50000000000000 : ℝ)^6211
        have hw : |(1069000829/2000000000 : ℝ)|=(1069000829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1134883831/5000000000 : ℝ)|^8259 ≤ (6959760367849/50000000000000 : ℝ)^6211
        have hw : |(-1134883831/5000000000 : ℝ)|=(1134883831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264359457/10000000000 : ℝ)|^8259 ≤ (1704208328313/4000000000000 : ℝ)^6211
        have hw : |(5264359457/10000000000 : ℝ)|=(5264359457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s7_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345004217/10000000000 : ℝ)*x 0 + (131608983/250000000 : ℝ)*x 1 + (-1134883873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345004217/10000000000 : ℝ)^8259 ≤ (21737635912643/50000000000000 : ℝ)^6211 := by
    have hnat : (5345004217 : ℕ)^8259*50000000000000^6211 ≤ 21737635912643^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345004217 10000000000 21737635912643 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131608983/250000000 : ℝ)^8259 ≤ (8521041346693/20000000000000 : ℝ)^6211 := by
    have hnat : (131608983 : ℕ)^8259*20000000000000^6211 ≤ 8521041346693^6211*250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131608983 250000000 8521041346693 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134883873/5000000000 : ℝ)^8259 ≤ (6959760710347/50000000000000 : ℝ)^6211 := by
    have hnat : (1134883873 : ℕ)^8259*50000000000000^6211 ≤ 6959760710347^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134883873 5000000000 6959760710347 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345004217/10000000000 : ℝ), (131608983/250000000 : ℝ), (-1134883873/5000000000 : ℝ)] ![(21737635912643/50000000000000 : ℝ), (8521041346693/20000000000000 : ℝ), (6959760710347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345004217/10000000000 : ℝ)|^8259 ≤ (21737635912643/50000000000000 : ℝ)^6211
        have hw : |(5345004217/10000000000 : ℝ)|=(5345004217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131608983/250000000 : ℝ)|^8259 ≤ (8521041346693/20000000000000 : ℝ)^6211
        have hw : |(131608983/250000000 : ℝ)|=(131608983/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134883873/5000000000 : ℝ)|^8259 ≤ (6959760710347/50000000000000 : ℝ)^6211
        have hw : |(-1134883873/5000000000 : ℝ)|=(1134883873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s7_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187743651/5000000000 : ℝ)*x 0 + (66404417/156250000 : ℝ)*x 1 + (4504855023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187743651/5000000000 : ℝ)^8259 ≤ (33316498926099/100000000000000 : ℝ)^6211 := by
    have hnat : (2187743651 : ℕ)^8259*100000000000000^6211 ≤ 33316498926099^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187743651 5000000000 33316498926099 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66404417/156250000 : ℝ)^8259 ≤ (128203196091/400000000000 : ℝ)^6211 := by
    have hnat : (66404417 : ℕ)^8259*400000000000^6211 ≤ 128203196091^6211*156250000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66404417 156250000 128203196091 400000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504855023/10000000000 : ℝ)^8259 ≤ (17316351013581/50000000000000 : ℝ)^6211 := by
    have hnat : (4504855023 : ℕ)^8259*50000000000000^6211 ≤ 17316351013581^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504855023 10000000000 17316351013581 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187743651/5000000000 : ℝ), (66404417/156250000 : ℝ), (4504855023/10000000000 : ℝ)] ![(33316498926099/100000000000000 : ℝ), (128203196091/400000000000 : ℝ), (17316351013581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187743651/5000000000 : ℝ)|^8259 ≤ (33316498926099/100000000000000 : ℝ)^6211
        have hw : |(2187743651/5000000000 : ℝ)|=(2187743651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66404417/156250000 : ℝ)|^8259 ≤ (128203196091/400000000000 : ℝ)^6211
        have hw : |(66404417/156250000 : ℝ)|=(66404417/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504855023/10000000000 : ℝ)|^8259 ≤ (17316351013581/50000000000000 : ℝ)^6211
        have hw : |(4504855023/10000000000 : ℝ)|=(4504855023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s7_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1101882077/5000000000 : ℝ)*x 0 + (5264685737/10000000000 : ℝ)*x 1 + (674266137/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1101882077/5000000000 : ℝ)^8259 ≤ (6691939176579/50000000000000 : ℝ)^6211 := by
    have hnat : (1101882077 : ℕ)^8259*50000000000000^6211 ≤ 6691939176579^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101882077 5000000000 6691939176579 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264685737/10000000000 : ℝ)^8259 ≤ (5326089948633/12500000000000 : ℝ)^6211 := by
    have hnat : (5264685737 : ℕ)^8259*12500000000000^6211 ≤ 5326089948633^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264685737 10000000000 5326089948633 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674266137/1250000000 : ℝ)^8259 ≤ (44007402039101/100000000000000 : ℝ)^6211 := by
    have hnat : (674266137 : ℕ)^8259*100000000000000^6211 ≤ 44007402039101^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674266137 1250000000 44007402039101 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1101882077/5000000000 : ℝ), (5264685737/10000000000 : ℝ), (674266137/1250000000 : ℝ)] ![(6691939176579/50000000000000 : ℝ), (5326089948633/12500000000000 : ℝ), (44007402039101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1101882077/5000000000 : ℝ)|^8259 ≤ (6691939176579/50000000000000 : ℝ)^6211
        have hw : |(-1101882077/5000000000 : ℝ)|=(1101882077/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264685737/10000000000 : ℝ)|^8259 ≤ (5326089948633/12500000000000 : ℝ)^6211
        have hw : |(5264685737/10000000000 : ℝ)|=(5264685737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674266137/1250000000 : ℝ)|^8259 ≤ (44007402039101/100000000000000 : ℝ)^6211
        have hw : |(674266137/1250000000 : ℝ)|=(674266137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s7_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328058799/2500000000 : ℝ)*x 0 + (-534999507/2500000000 : ℝ)*x 1 + (674266137/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328058799/2500000000 : ℝ)^8259 ≤ (5390150765457/12500000000000 : ℝ)^6211 := by
    have hnat : (1328058799 : ℕ)^8259*12500000000000^6211 ≤ 5390150765457^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328058799 2500000000 5390150765457 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534999507/2500000000 : ℝ)^8259 ≤ (12871391822017/100000000000000 : ℝ)^6211 := by
    have hnat : (534999507 : ℕ)^8259*100000000000000^6211 ≤ 12871391822017^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534999507 2500000000 12871391822017 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674266137/1250000000 : ℝ)^8259 ≤ (44007402039101/100000000000000 : ℝ)^6211 := by
    have hnat : (674266137 : ℕ)^8259*100000000000000^6211 ≤ 44007402039101^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674266137 1250000000 44007402039101 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328058799/2500000000 : ℝ), (-534999507/2500000000 : ℝ), (674266137/1250000000 : ℝ)] ![(5390150765457/12500000000000 : ℝ), (12871391822017/100000000000000 : ℝ), (44007402039101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328058799/2500000000 : ℝ)|^8259 ≤ (5390150765457/12500000000000 : ℝ)^6211
        have hw : |(1328058799/2500000000 : ℝ)|=(1328058799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534999507/2500000000 : ℝ)|^8259 ≤ (12871391822017/100000000000000 : ℝ)^6211
        have hw : |(-534999507/2500000000 : ℝ)|=(534999507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674266137/1250000000 : ℝ)|^8259 ≤ (44007402039101/100000000000000 : ℝ)^6211
        have hw : |(674266137/1250000000 : ℝ)|=(674266137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s7_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328058799/2500000000 : ℝ)*x 0 + (674266137/1250000000 : ℝ)*x 1 + (-534999507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328058799/2500000000 : ℝ)^8259 ≤ (5390150765457/12500000000000 : ℝ)^6211 := by
    have hnat : (1328058799 : ℕ)^8259*12500000000000^6211 ≤ 5390150765457^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328058799 2500000000 5390150765457 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674266137/1250000000 : ℝ)^8259 ≤ (44007402039101/100000000000000 : ℝ)^6211 := by
    have hnat : (674266137 : ℕ)^8259*100000000000000^6211 ≤ 44007402039101^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674266137 1250000000 44007402039101 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534999507/2500000000 : ℝ)^8259 ≤ (12871391822017/100000000000000 : ℝ)^6211 := by
    have hnat : (534999507 : ℕ)^8259*100000000000000^6211 ≤ 12871391822017^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534999507 2500000000 12871391822017 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328058799/2500000000 : ℝ), (674266137/1250000000 : ℝ), (-534999507/2500000000 : ℝ)] ![(5390150765457/12500000000000 : ℝ), (44007402039101/100000000000000 : ℝ), (12871391822017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328058799/2500000000 : ℝ)|^8259 ≤ (5390150765457/12500000000000 : ℝ)^6211
        have hw : |(1328058799/2500000000 : ℝ)|=(1328058799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674266137/1250000000 : ℝ)|^8259 ≤ (44007402039101/100000000000000 : ℝ)^6211
        have hw : |(674266137/1250000000 : ℝ)|=(674266137/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534999507/2500000000 : ℝ)|^8259 ≤ (12871391822017/100000000000000 : ℝ)^6211
        have hw : |(-534999507/2500000000 : ℝ)|=(534999507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s7_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4375497263/10000000000 : ℝ)*x 0 + (2252107747/5000000000 : ℝ)*x 1 + (850104907/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375497263/10000000000 : ℝ)^8259 ≤ (33316599782153/100000000000000 : ℝ)^6211 := by
    have hnat : (4375497263 : ℕ)^8259*100000000000000^6211 ≤ 33316599782153^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375497263 10000000000 33316599782153 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252107747/5000000000 : ℝ)^8259 ≤ (34626164378589/100000000000000 : ℝ)^6211 := by
    have hnat : (2252107747 : ℕ)^8259*100000000000000^6211 ≤ 34626164378589^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252107747 5000000000 34626164378589 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850104907/2000000000 : ℝ)^8259 ≤ (1602861791263/5000000000000 : ℝ)^6211 := by
    have hnat : (850104907 : ℕ)^8259*5000000000000^6211 ≤ 1602861791263^6211*2000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850104907 2000000000 1602861791263 5000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375497263/10000000000 : ℝ), (2252107747/5000000000 : ℝ), (850104907/2000000000 : ℝ)] ![(33316599782153/100000000000000 : ℝ), (34626164378589/100000000000000 : ℝ), (1602861791263/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375497263/10000000000 : ℝ)|^8259 ≤ (33316599782153/100000000000000 : ℝ)^6211
        have hw : |(4375497263/10000000000 : ℝ)|=(4375497263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252107747/5000000000 : ℝ)|^8259 ≤ (34626164378589/100000000000000 : ℝ)^6211
        have hw : |(2252107747/5000000000 : ℝ)|=(2252107747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(850104907/2000000000 : ℝ)|^8259 ≤ (1602861791263/5000000000000 : ℝ)^6211
        have hw : |(850104907/2000000000 : ℝ)|=(850104907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2801/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2803/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2803/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2803/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2803/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2803/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2803/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (281/2500 : ℝ) ^ (4129/1024 : ℝ) ≤ (7437803670585631/50000000000000000000 : ℝ) := by
    have hpowers : (281/2500 : ℝ)^4129 ≤ (7437803670585631/50000000000000000000 : ℝ)^1024 := by
      have hnat : (281 : ℕ)^4129*50000000000000000000^1024 ≤ 7437803670585631^1024*2500^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2500 7437803670585631 50000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2500 : ℝ)) (X := (7437803670585631/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2803/20000 : ℝ) ^ (4129/1024 : ℝ) ≤ (36213461364723199/100000000000000000000 : ℝ) := by
    have hpowers : (2803/20000 : ℝ)^4129 ≤ (36213461364723199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2803 : ℕ)^4129*100000000000000000000^1024 ≤ 36213461364723199^1024*20000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2803 20000 36213461364723199 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2803/20000 : ℝ)) (X := (36213461364723199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007437803670585631/25000000000000000000 : ℝ) ≤ (10000737753365323/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25007437803670585631/25000000000000000000 : ℝ)^1024 ≤ (10000737753365323/10000000000000000 : ℝ)^4129 := by
      have hnat : (25007437803670585631 : ℕ)^1024*10000000000000000^4129 ≤ 10000737753365323^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007437803670585631 25000000000000000000 10000737753365323 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000737753365323/10000000000000000 : ℝ)) (X := (25007437803670585631/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051089068705894461/100000000000000000000 : ℝ) ≤ (5000633387743931/5000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (100051089068705894461/100000000000000000000 : ℝ)^1024 ≤ (5000633387743931/5000000000000000 : ℝ)^4129 := by
      have hnat : (100051089068705894461 : ℕ)^1024*5000000000000000^4129 ≤ 5000633387743931^4129*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051089068705894461 100000000000000000000 5000633387743931 5000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000633387743931/5000000000000000 : ℝ)) (X := (100051089068705894461/100000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036213461364723199/50000000000000000000 : ℝ) ≤ (10001795797610401/10000000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50036213461364723199/50000000000000000000 : ℝ)^1024 ≤ (10001795797610401/10000000000000000 : ℝ)^4129 := by
      have hnat : (50036213461364723199 : ℕ)^1024*10000000000000000^4129 ≤ 10001795797610401^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036213461364723199 50000000000000000000 10001795797610401 10000000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001795797610401/10000000000000000 : ℝ)) (X := (50036213461364723199/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7437803670585631/50000000000000000000 : ℝ) ≤ ((1849343656551606307/1850000000000000000 : ℝ)+2*(176340707513/92500000000000 : ℝ)*(281/2500 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (1849343656551606307/1850000000000000000 : ℝ)+2*(176340707513/92500000000000 : ℝ)*(281/2500 : ℝ)=(10000737753365323/10000000000000000 : ℝ) by norm_num, show 1+2*(7437803670585631/50000000000000000000 : ℝ)=(25007437803670585631/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36213461364723199/100000000000000000000 : ℝ)+(7437803670585631/50000000000000000000 : ℝ) ≤ ((1849343656551606307/1850000000000000000 : ℝ)+(176340707513/92500000000000 : ℝ)*((2803/20000 : ℝ)+(281/2500 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (1849343656551606307/1850000000000000000 : ℝ)+(176340707513/92500000000000 : ℝ)*((2803/20000 : ℝ)+(281/2500 : ℝ))=(5000633387743931/5000000000000000 : ℝ) by norm_num, show 1+(36213461364723199/100000000000000000000 : ℝ)+(7437803670585631/50000000000000000000 : ℝ)=(100051089068705894461/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36213461364723199/100000000000000000000 : ℝ) ≤ ((1849343656551606307/1850000000000000000 : ℝ)+2*(176340707513/92500000000000 : ℝ)*(2803/20000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (1849343656551606307/1850000000000000000 : ℝ)+2*(176340707513/92500000000000 : ℝ)*(2803/20000 : ℝ)=(10001795797610401/10000000000000000 : ℝ) by norm_num, show 1+2*(36213461364723199/100000000000000000000 : ℝ)=(50036213461364723199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1849343656551606307/1850000000000000000 : ℝ)*(X 1 0+X 2 0)+(176340707513/92500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (1849343656551606307/1850000000000000000 : ℝ)) (alpha := (176340707513/92500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1849343656551606307/1850000000000000000 : ℝ)*(X 0 1+X 2 1)+(176340707513/92500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (1849343656551606307/1850000000000000000 : ℝ)) (alpha := (176340707513/92500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1849343656551606307/1850000000000000000 : ℝ)*(X 0 2+X 1 2)+(176340707513/92500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (2803/20000 : ℝ)) (c := (1849343656551606307/1850000000000000000 : ℝ)) (alpha := (176340707513/92500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-550939791/2500000000 : ℝ)*X 0 0+(5394456661/10000000000 : ℝ)*X 0 1+(1316089819/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069000829/2000000000 : ℝ)*X 1 0+(-1134883831/5000000000 : ℝ)*X 1 1+(5264359457/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345004217/10000000000 : ℝ)*X 2 0+(131608983/250000000 : ℝ)*X 2 1+(-1134883873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187743651/5000000000 : ℝ)*X 0 0+(66404417/156250000 : ℝ)*X 0 1+(4504855023/10000000000 : ℝ)*X 0 2+(2187743651/5000000000 : ℝ)*X 1 0+(66404417/156250000 : ℝ)*X 1 1+(4504855023/10000000000 : ℝ)*X 1 2+(2187743651/5000000000 : ℝ)*X 2 0+(66404417/156250000 : ℝ)*X 2 1+(4504855023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1101882077/5000000000 : ℝ)*X 0 0+(5264685737/10000000000 : ℝ)*X 0 1+(674266137/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328058799/2500000000 : ℝ)*X 1 0+(-534999507/2500000000 : ℝ)*X 1 1+(674266137/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328058799/2500000000 : ℝ)*X 2 0+(674266137/1250000000 : ℝ)*X 2 1+(-534999507/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4375497263/10000000000 : ℝ)*X 0 0+(2252107747/5000000000 : ℝ)*X 0 1+(850104907/2000000000 : ℝ)*X 0 2+(4375497263/10000000000 : ℝ)*X 1 0+(2252107747/5000000000 : ℝ)*X 1 1+(850104907/2000000000 : ℝ)*X 1 2+(4375497263/10000000000 : ℝ)*X 2 0+(2252107747/5000000000 : ℝ)*X 2 1+(850104907/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5568392294809397827857/578125000000000000000000000 : ℝ) := by norm_num
    linear_combination (2116461977/100000000000000 : ℝ)*(base19) + (2219687241/100000000000000 : ℝ)*(base23) + (34033/20000000000000 : ℝ)*(lower2) + (291462447/100000000000000 : ℝ)*(upper3) + (178020521/100000000000000 : ℝ)*(upper5) + (5804370803857429/100000000000000 : ℝ)*(major0) + (5804370803857429/100000000000000 : ℝ)*(major1) + (5804370803857429/100000000000000 : ℝ)*(major2) + (7686619129723989/100000000000000 : ℝ)*(sp0) + (7686682509758543/100000000000000 : ℝ)*(sp1) + (7686682406533279/100000000000000 : ℝ)*(sp2) + (1961011946345097/50000000000000 : ℝ)*(sp3) + (65496496531/100000000000000 : ℝ)*(sp4) + (32767743677/100000000000000 : ℝ)*(sp7) + (392205666043387/10000000000000 : ℝ)*(f.failure) + (192167115655513/2500000000000 : ℝ)*(f.sum) + (590026006881/578125000000000000000000000 : ℝ)*base66 + (1081744552363255297/185000000000000000000000000000000 : ℝ)*base68 + (526962609601744703/185000000000000000000000000000000 : ℝ)*base69 + (2102008990856744703/185000000000000000000000000000000 : ℝ)*base71 + (21133494889423/4625000000000000000000000000 : ℝ)*base74 + (4632049734433255297/185000000000000000000000000000000 : ℝ)*base76 + (1472501218623255297/185000000000000000000000000000000 : ℝ)*base78 + (691371074896744703/185000000000000000000000000000000 : ℝ)*base79 + (2172158122601/2312500000000000000000000000 : ℝ)*base81 + (4030147/500000000000000000000 : ℝ)*base90 + (4030147/500000000000000000000 : ℝ)*base92 + (4030147/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15982350201555752977756917/2890625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1030511847/100000000000000 : ℝ)*(base19) + (280218919/25000000000000 : ℝ)*(base23) + (55481643/50000000000000 : ℝ)*(upper3) + (41139277/100000000000000 : ℝ)*(lower4) + (56626917/50000000000000 : ℝ)*(upper5) + (364599667801327/6250000000000 : ℝ)*(major0) + (364599667801327/6250000000000 : ℝ)*(major1) + (364599667801327/6250000000000 : ℝ)*(major2) + (7006206707/25000000000000 : ℝ)*(sp1) + (30119461947/100000000000000 : ℝ)*(sp2) + (7725385730491647/100000000000000 : ℝ)*(sp4) + (1931339168788243/25000000000000 : ℝ)*(sp5) + (965669311269253/12500000000000 : ℝ)*(sp6) + (3941803454849837/100000000000000 : ℝ)*(sp7) + (3941803454849837/100000000000000 : ℝ)*(f.failure) + (7725385730491647/100000000000000 : ℝ)*(f.sum) + (20000859785891/4625000000000000000000000000 : ℝ)*base65 + (1221788536623111/11562500000000000000000000000000 : ℝ)*base68 + (41524022233498111/11562500000000000000000000000000 : ℝ)*base70 + (101790982312751889/11562500000000000000000000000000 : ℝ)*base71 + (5788154179133/2312500000000000000000000000 : ℝ)*base73 + (178164150374748111/11562500000000000000000000000000 : ℝ)*base76 + (96277586858185611/11562500000000000000000000000000 : ℝ)*base78 + (6958401563185611/11562500000000000000000000000000 : ℝ)*base80 + (10263059741109/4625000000000000000000000000 : ℝ)*base82 + (5717403/5000000000000000000000 : ℝ)*base89 + (5717403/5000000000000000000000 : ℝ)*base91 + (5717403/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1066_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2803/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1066_s8_0 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-550942479/2500000000 : ℝ)*x 0 + (674294251/1250000000 : ℝ)*x 1 + (526445469/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (550942479/2500000000 : ℝ)^8259 ≤ (6691962442821/50000000000000 : ℝ)^6211 := by
    have hnat : (550942479 : ℕ)^8259*50000000000000^6211 ≤ 6691962442821^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550942479 2500000000 6691962442821 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674294251/1250000000 : ℝ)^8259 ≤ (11002460504323/25000000000000 : ℝ)^6211 := by
    have hnat : (674294251 : ℕ)^8259*25000000000000^6211 ≤ 11002460504323^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674294251 1250000000 11002460504323 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526445469/1000000000 : ℝ)^8259 ≤ (21303116542539/50000000000000 : ℝ)^6211 := by
    have hnat : (526445469 : ℕ)^8259*50000000000000^6211 ≤ 21303116542539^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526445469 1000000000 21303116542539 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-550942479/2500000000 : ℝ), (674294251/1250000000 : ℝ), (526445469/1000000000 : ℝ)] ![(6691962442821/50000000000000 : ℝ), (11002460504323/25000000000000 : ℝ), (21303116542539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-550942479/2500000000 : ℝ)|^8259 ≤ (6691962442821/50000000000000 : ℝ)^6211
        have hw : |(-550942479/2500000000 : ℝ)|=(550942479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674294251/1250000000 : ℝ)|^8259 ≤ (11002460504323/25000000000000 : ℝ)^6211
        have hw : |(674294251/1250000000 : ℝ)|=(674294251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526445469/1000000000 : ℝ)|^8259 ≤ (21303116542539/50000000000000 : ℝ)^6211
        have hw : |(526445469/1000000000 : ℝ)|=(526445469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s8_1 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (133624449/250000000 : ℝ)*x 0 + (-2269676659/10000000000 : ℝ)*x 1 + (526445473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133624449/250000000 : ℝ)^8259 ≤ (43474987834047/100000000000000 : ℝ)^6211 := by
    have hnat : (133624449 : ℕ)^8259*100000000000000^6211 ≤ 43474987834047^6211*250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133624449 250000000 43474987834047 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269676659/10000000000 : ℝ)^8259 ≤ (13918778637027/100000000000000 : ℝ)^6211 := by
    have hnat : (2269676659 : ℕ)^8259*100000000000000^6211 ≤ 13918778637027^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269676659 10000000000 13918778637027 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526445473/1000000000 : ℝ)^8259 ≤ (852124670311/2000000000000 : ℝ)^6211 := by
    have hnat : (526445473 : ℕ)^8259*2000000000000^6211 ≤ 852124670311^6211*1000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526445473 1000000000 852124670311 2000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133624449/250000000 : ℝ), (-2269676659/10000000000 : ℝ), (526445473/1000000000 : ℝ)] ![(43474987834047/100000000000000 : ℝ), (13918778637027/100000000000000 : ℝ), (852124670311/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133624449/250000000 : ℝ)|^8259 ≤ (43474987834047/100000000000000 : ℝ)^6211
        have hw : |(133624449/250000000 : ℝ)|=(133624449/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2269676659/10000000000 : ℝ)|^8259 ≤ (13918778637027/100000000000000 : ℝ)^6211
        have hw : |(-2269676659/10000000000 : ℝ)|=(2269676659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526445473/1000000000 : ℝ)|^8259 ≤ (852124670311/2000000000000 : ℝ)^6211
        have hw : |(526445473/1000000000 : ℝ)|=(526445473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s8_2 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106899559/200000000 : ℝ)*x 0 + (2632227373/5000000000 : ℝ)*x 1 + (-2269676651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106899559/200000000 : ℝ)^8259 ≤ (43474987725889/100000000000000 : ℝ)^6211 := by
    have hnat : (106899559 : ℕ)^8259*100000000000000^6211 ≤ 43474987725889^6211*200000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106899559 200000000 43474987725889 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632227373/5000000000 : ℝ)^8259 ≤ (42606233687739/100000000000000 : ℝ)^6211 := by
    have hnat : (2632227373 : ℕ)^8259*100000000000000^6211 ≤ 42606233687739^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632227373 5000000000 42606233687739 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2269676651/10000000000 : ℝ)^8259 ≤ (1391877857179/10000000000000 : ℝ)^6211 := by
    have hnat : (2269676651 : ℕ)^8259*10000000000000^6211 ≤ 1391877857179^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269676651 10000000000 1391877857179 10000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106899559/200000000 : ℝ), (2632227373/5000000000 : ℝ), (-2269676651/10000000000 : ℝ)] ![(43474987725889/100000000000000 : ℝ), (42606233687739/100000000000000 : ℝ), (1391877857179/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106899559/200000000 : ℝ)|^8259 ≤ (43474987725889/100000000000000 : ℝ)^6211
        have hw : |(106899559/200000000 : ℝ)|=(106899559/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632227373/5000000000 : ℝ)|^8259 ≤ (42606233687739/100000000000000 : ℝ)^6211
        have hw : |(2632227373/5000000000 : ℝ)|=(2632227373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2269676651/10000000000 : ℝ)|^8259 ≤ (1391877857179/10000000000000 : ℝ)^6211
        have hw : |(-2269676651/10000000000 : ℝ)|=(2269676651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s8_3 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1093873081/2500000000 : ℝ)*x 0 + (2125037977/5000000000 : ℝ)*x 1 + (2252330229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1093873081/2500000000 : ℝ)^8259 ≤ (8329137443577/25000000000000 : ℝ)^6211 := by
    have hnat : (1093873081 : ℕ)^8259*25000000000000^6211 ≤ 8329137443577^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093873081 2500000000 8329137443577 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125037977/5000000000 : ℝ)^8259 ≤ (32052737169111/100000000000000 : ℝ)^6211 := by
    have hnat : (2125037977 : ℕ)^8259*100000000000000^6211 ≤ 32052737169111^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125037977 5000000000 32052737169111 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252330229/5000000000 : ℝ)^8259 ≤ (17315356517389/50000000000000 : ℝ)^6211 := by
    have hnat : (2252330229 : ℕ)^8259*50000000000000^6211 ≤ 17315356517389^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252330229 5000000000 17315356517389 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1093873081/2500000000 : ℝ), (2125037977/5000000000 : ℝ), (2252330229/5000000000 : ℝ)] ![(8329137443577/25000000000000 : ℝ), (32052737169111/100000000000000 : ℝ), (17315356517389/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1093873081/2500000000 : ℝ)|^8259 ≤ (8329137443577/25000000000000 : ℝ)^6211
        have hw : |(1093873081/2500000000 : ℝ)|=(1093873081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125037977/5000000000 : ℝ)|^8259 ≤ (32052737169111/100000000000000 : ℝ)^6211
        have hw : |(2125037977/5000000000 : ℝ)|=(2125037977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252330229/5000000000 : ℝ)|^8259 ≤ (17315356517389/50000000000000 : ℝ)^6211
        have hw : |(2252330229/5000000000 : ℝ)|=(2252330229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s8_4 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203775013/10000000000 : ℝ)*x 0 + (5264780077/10000000000 : ℝ)*x 1 + (215761097/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203775013/10000000000 : ℝ)^8259 ≤ (2676793209557/20000000000000 : ℝ)^6211 := by
    have hnat : (2203775013 : ℕ)^8259*20000000000000^6211 ≤ 2676793209557^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203775013 10000000000 2676793209557 20000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264780077/10000000000 : ℝ)^8259 ≤ (42609734876761/100000000000000 : ℝ)^6211 := by
    have hnat : (5264780077 : ℕ)^8259*100000000000000^6211 ≤ 42609734876761^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264780077 10000000000 42609734876761 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215761097/400000000 : ℝ)^8259 ≤ (44006299063063/100000000000000 : ℝ)^6211 := by
    have hnat : (215761097 : ℕ)^8259*100000000000000^6211 ≤ 44006299063063^6211*400000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215761097 400000000 44006299063063 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203775013/10000000000 : ℝ), (5264780077/10000000000 : ℝ), (215761097/400000000 : ℝ)] ![(2676793209557/20000000000000 : ℝ), (42609734876761/100000000000000 : ℝ), (44006299063063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203775013/10000000000 : ℝ)|^8259 ≤ (2676793209557/20000000000000 : ℝ)^6211
        have hw : |(-2203775013/10000000000 : ℝ)|=(2203775013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264780077/10000000000 : ℝ)|^8259 ≤ (42609734876761/100000000000000 : ℝ)^6211
        have hw : |(5264780077/10000000000 : ℝ)|=(5264780077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215761097/400000000 : ℝ)|^8259 ≤ (44006299063063/100000000000000 : ℝ)^6211
        have hw : |(215761097/400000000 : ℝ)|=(215761097/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s8_5 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (106245177/200000000 : ℝ)*x 0 + (-2140103883/10000000000 : ℝ)*x 1 + (5394027519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106245177/200000000 : ℝ)^8259 ≤ (43121461443431/100000000000000 : ℝ)^6211 := by
    have hnat : (106245177 : ℕ)^8259*100000000000000^6211 ≤ 43121461443431^6211*200000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106245177 200000000 43121461443431 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140103883/10000000000 : ℝ)^8259 ≤ (12872238450729/100000000000000 : ℝ)^6211 := by
    have hnat : (2140103883 : ℕ)^8259*100000000000000^6211 ≤ 12872238450729^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140103883 10000000000 12872238450729 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394027519/10000000000 : ℝ)^8259 ≤ (22003150041409/50000000000000 : ℝ)^6211 := by
    have hnat : (5394027519 : ℕ)^8259*50000000000000^6211 ≤ 22003150041409^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394027519 10000000000 22003150041409 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106245177/200000000 : ℝ), (-2140103883/10000000000 : ℝ), (5394027519/10000000000 : ℝ)] ![(43121461443431/100000000000000 : ℝ), (12872238450729/100000000000000 : ℝ), (22003150041409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106245177/200000000 : ℝ)|^8259 ≤ (43121461443431/100000000000000 : ℝ)^6211
        have hw : |(106245177/200000000 : ℝ)|=(106245177/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140103883/10000000000 : ℝ)|^8259 ≤ (12872238450729/100000000000000 : ℝ)^6211
        have hw : |(-2140103883/10000000000 : ℝ)|=(2140103883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394027519/10000000000 : ℝ)|^8259 ≤ (22003150041409/50000000000000 : ℝ)^6211
        have hw : |(5394027519/10000000000 : ℝ)|=(5394027519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s8_6 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656129413/5000000000 : ℝ)*x 0 + (215761101/400000000 : ℝ)*x 1 + (-535025977/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656129413/5000000000 : ℝ)^8259 ≤ (5390182648047/12500000000000 : ℝ)^6211 := by
    have hnat : (2656129413 : ℕ)^8259*12500000000000^6211 ≤ 5390182648047^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656129413 5000000000 5390182648047 12500000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215761101/400000000 : ℝ)^8259 ≤ (11001575036977/25000000000000 : ℝ)^6211 := by
    have hnat : (215761101 : ℕ)^8259*25000000000000^6211 ≤ 11001575036977^6211*400000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215761101 400000000 11001575036977 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (535025977/2500000000 : ℝ)^8259 ≤ (12872238650681/100000000000000 : ℝ)^6211 := by
    have hnat : (535025977 : ℕ)^8259*100000000000000^6211 ≤ 12872238650681^6211*2500000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535025977 2500000000 12872238650681 100000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656129413/5000000000 : ℝ), (215761101/400000000 : ℝ), (-535025977/2500000000 : ℝ)] ![(5390182648047/12500000000000 : ℝ), (11001575036977/25000000000000 : ℝ), (12872238650681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656129413/5000000000 : ℝ)|^8259 ≤ (5390182648047/12500000000000 : ℝ)^6211
        have hw : |(2656129413/5000000000 : ℝ)|=(2656129413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215761101/400000000 : ℝ)|^8259 ≤ (11001575036977/25000000000000 : ℝ)^6211
        have hw : |(215761101/400000000 : ℝ)|=(215761101/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-535025977/2500000000 : ℝ)|^8259 ≤ (12872238650681/100000000000000 : ℝ)^6211
        have hw : |(-535025977/2500000000 : ℝ)|=(535025977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1066_s8_7 (p : ℝ) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546937803/1250000000 : ℝ)*x 0 + (4504022643/10000000000 : ℝ)*x 1 + (2125357947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546937803/1250000000 : ℝ)^8259 ≤ (8329163009447/25000000000000 : ℝ)^6211 := by
    have hnat : (546937803 : ℕ)^8259*25000000000000^6211 ≤ 8329163009447^6211*1250000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546937803 1250000000 8329163009447 25000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504022643/10000000000 : ℝ)^8259 ≤ (17312096500097/50000000000000 : ℝ)^6211 := by
    have hnat : (4504022643 : ℕ)^8259*50000000000000^6211 ≤ 17312096500097^6211*10000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504022643 10000000000 17312096500097 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125357947/5000000000 : ℝ)^8259 ≤ (16029577471451/50000000000000 : ℝ)^6211 := by
    have hnat : (2125357947 : ℕ)^8259*50000000000000^6211 ≤ 16029577471451^6211*5000000000^8259 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125357947 5000000000 16029577471451 50000000000000 8259 6211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8259/2048 : ℝ)) 8259 6211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546937803/1250000000 : ℝ), (4504022643/10000000000 : ℝ), (2125357947/5000000000 : ℝ)] ![(8329163009447/25000000000000 : ℝ), (17312096500097/50000000000000 : ℝ), (16029577471451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546937803/1250000000 : ℝ)|^8259 ≤ (8329163009447/25000000000000 : ℝ)^6211
        have hw : |(546937803/1250000000 : ℝ)|=(546937803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504022643/10000000000 : ℝ)|^8259 ≤ (17312096500097/50000000000000 : ℝ)^6211
        have hw : |(4504022643/10000000000 : ℝ)|=(4504022643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125357947/5000000000 : ℝ)|^8259 ≤ (16029577471451/50000000000000 : ℝ)^6211
        have hw : |(2125357947/5000000000 : ℝ)|=(2125357947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1066_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11251/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14003/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2801/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2801/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11249/100000 : ℝ) ^ (4129/1024 : ℝ) ≤ (2984738764889609/20000000000000000000 : ℝ) := by
    have hpowers : (11249/100000 : ℝ)^4129 ≤ (2984738764889609/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11249 : ℕ)^4129*20000000000000000000^1024 ≤ 2984738764889609^1024*100000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11249 100000 2984738764889609 20000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11249/100000 : ℝ)) (X := (2984738764889609/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2801/20000 : ℝ) ^ (4129/1024 : ℝ) ≤ (36109385021628327/100000000000000000000 : ℝ) := by
    have hpowers : (2801/20000 : ℝ)^4129 ≤ (36109385021628327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2801 : ℕ)^4129*100000000000000000000^1024 ≤ 36109385021628327^1024*20000^4129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2801 20000 36109385021628327 100000000000000000000 4129 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2801/20000 : ℝ)) (X := (36109385021628327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002984738764889609/10000000000000000000 : ℝ) ≤ (2500185034484797/2500000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (10002984738764889609/10000000000000000000 : ℝ)^1024 ≤ (2500185034484797/2500000000000000 : ℝ)^4129 := by
      have hnat : (10002984738764889609 : ℕ)^1024*2500000000000000^4129 ≤ 2500185034484797^4129*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002984738764889609 10000000000000000000 2500185034484797 2500000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185034484797/2500000000000000 : ℝ)) (X := (10002984738764889609/10000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012758269711519093/25000000000000000000 : ℝ) ≤ (2500316346865357/2500000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (25012758269711519093/25000000000000000000 : ℝ)^1024 ≤ (2500316346865357/2500000000000000 : ℝ)^4129 := by
      have hnat : (25012758269711519093 : ℕ)^1024*2500000000000000^4129 ≤ 2500316346865357^4129*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012758269711519093 25000000000000000000 2500316346865357 2500000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500316346865357/2500000000000000 : ℝ)) (X := (25012758269711519093/25000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036109385021628327/50000000000000000000 : ℝ) ≤ (2500447659245917/2500000000000000 : ℝ) ^ (4129/1024 : ℝ) := by
    have hpowers : (50036109385021628327/50000000000000000000 : ℝ)^1024 ≤ (2500447659245917/2500000000000000 : ℝ)^4129 := by
      have hnat : (50036109385021628327 : ℕ)^1024*2500000000000000^4129 ≤ 2500447659245917^4129*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036109385021628327 50000000000000000000 2500447659245917 2500000000000000 1024 4129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500447659245917/2500000000000000 : ℝ)) (X := (50036109385021628327/50000000000000000000 : ℝ)) (by norm_num) 4129 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2984738764889609/20000000000000000000 : ℝ) ≤ ((1721888922275565413/1722500000000000000 : ℝ)+2*(1641404757/861250000000 : ℝ)*(11249/100000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (1721888922275565413/1722500000000000000 : ℝ)+2*(1641404757/861250000000 : ℝ)*(11249/100000 : ℝ)=(2500185034484797/2500000000000000 : ℝ) by norm_num, show 1+2*(2984738764889609/20000000000000000000 : ℝ)=(10002984738764889609/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36109385021628327/100000000000000000000 : ℝ)+(2984738764889609/20000000000000000000 : ℝ) ≤ ((1721888922275565413/1722500000000000000 : ℝ)+(1641404757/861250000000 : ℝ)*((2801/20000 : ℝ)+(11249/100000 : ℝ)))^(4129/1024 : ℝ) := by
    rw [show (1721888922275565413/1722500000000000000 : ℝ)+(1641404757/861250000000 : ℝ)*((2801/20000 : ℝ)+(11249/100000 : ℝ))=(2500316346865357/2500000000000000 : ℝ) by norm_num, show 1+(36109385021628327/100000000000000000000 : ℝ)+(2984738764889609/20000000000000000000 : ℝ)=(25012758269711519093/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36109385021628327/100000000000000000000 : ℝ) ≤ ((1721888922275565413/1722500000000000000 : ℝ)+2*(1641404757/861250000000 : ℝ)*(2801/20000 : ℝ))^(4129/1024 : ℝ) := by
    rw [show (1721888922275565413/1722500000000000000 : ℝ)+2*(1641404757/861250000000 : ℝ)*(2801/20000 : ℝ)=(2500447659245917/2500000000000000 : ℝ) by norm_num, show 1+2*(36109385021628327/100000000000000000000 : ℝ)=(50036109385021628327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1721888922275565413/1722500000000000000 : ℝ)*(X 1 0+X 2 0)+(1641404757/861250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (1721888922275565413/1722500000000000000 : ℝ)) (alpha := (1641404757/861250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1721888922275565413/1722500000000000000 : ℝ)*(X 0 1+X 2 1)+(1641404757/861250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (1721888922275565413/1722500000000000000 : ℝ)) (alpha := (1641404757/861250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1721888922275565413/1722500000000000000 : ℝ)*(X 0 2+X 1 2)+(1641404757/861250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4129/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (2801/20000 : ℝ)) (c := (1721888922275565413/1722500000000000000 : ℝ)) (alpha := (1641404757/861250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-550942479/2500000000 : ℝ)*X 0 0+(674294251/1250000000 : ℝ)*X 0 1+(526445469/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133624449/250000000 : ℝ)*X 1 0+(-2269676659/10000000000 : ℝ)*X 1 1+(526445473/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106899559/200000000 : ℝ)*X 2 0+(2632227373/5000000000 : ℝ)*X 2 1+(-2269676651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1093873081/2500000000 : ℝ)*X 0 0+(2125037977/5000000000 : ℝ)*X 0 1+(2252330229/5000000000 : ℝ)*X 0 2+(1093873081/2500000000 : ℝ)*X 1 0+(2125037977/5000000000 : ℝ)*X 1 1+(2252330229/5000000000 : ℝ)*X 1 2+(1093873081/2500000000 : ℝ)*X 2 0+(2125037977/5000000000 : ℝ)*X 2 1+(2252330229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2203775013/10000000000 : ℝ)*X 0 0+(5264780077/10000000000 : ℝ)*X 0 1+(215761097/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((106245177/200000000 : ℝ)*X 1 0+(-2140103883/10000000000 : ℝ)*X 1 1+(5394027519/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656129413/5000000000 : ℝ)*X 2 0+(215761101/400000000 : ℝ)*X 2 1+(-535025977/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546937803/1250000000 : ℝ)*X 0 0+(4504022643/10000000000 : ℝ)*X 0 1+(2125357947/5000000000 : ℝ)*X 0 2+(546937803/1250000000 : ℝ)*X 1 0+(4504022643/10000000000 : ℝ)*X 1 1+(2125357947/5000000000 : ℝ)*X 1 2+(546937803/1250000000 : ℝ)*X 2 0+(4504022643/10000000000 : ℝ)*X 2 1+(2125357947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1066_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (281148889588300965195861/26500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2117183251/100000000000000 : ℝ)*(base19) + (125557997/6250000000000 : ℝ)*(base23) + (5016383/10000000000000 : ℝ)*(lower2) + (12530699/5000000000000 : ℝ)*(upper3) + (95237699/50000000000000 : ℝ)*(upper5) + (23252845142813/400000000000 : ℝ)*(major0) + (23252845142813/400000000000 : ℝ)*(major1) + (23252845142813/400000000000 : ℝ)*(major2) + (1539666313056023/20000000000000 : ℝ)*(sp0) + (7698389860598077/100000000000000 : ℝ)*(sp1) + (7698389968853377/100000000000000 : ℝ)*(sp2) + (785599728686131/20000000000000 : ℝ)*(sp3) + (60412501213/100000000000000 : ℝ)*(sp4) + (315965481/1000000000000 : ℝ)*(sp7) + (1964015119989377/50000000000000 : ℝ)*(f.failure) + (481149498611333/6250000000000 : ℝ)*(f.sum) + (118697725917/53000000000000000000000000 : ℝ)*base65 + (829350734925213/53000000000000000000000000000 : ℝ)*base67 + (433863951903213/53000000000000000000000000000 : ℝ)*base69 + (565264078671787/53000000000000000000000000000 : ℝ)*base72 + (182104916369/53000000000000000000000000 : ℝ)*base73 + (500204140148213/53000000000000000000000000000 : ℝ)*base75 + (187090752861787/53000000000000000000000000000 : ℝ)*base78 + (681369810112213/53000000000000000000000000000 : ℝ)*base79 + (210924856961/53000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (35021337/2500000000000000000000 : ℝ)*base90 + (35021337/2500000000000000000000 : ℝ)*base92 + (35021337/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (911376007007813701473/137800000000000000000000000 : ℝ) := by norm_num
    linear_combination (1377160307/100000000000000 : ℝ)*(base19) + (1467828221/100000000000000 : ℝ)*(base23) + (21953681/12500000000000 : ℝ)*(upper3) + (16082513/25000000000000 : ℝ)*(lower4) + (199104603/100000000000000 : ℝ)*(upper5) + (2921220809228907/50000000000000 : ℝ)*(major0) + (2921220809228907/50000000000000 : ℝ)*(major1) + (2921220809228907/50000000000000 : ℝ)*(major2) + (41012897761/100000000000000 : ℝ)*(sp1) + (20873829511/50000000000000 : ℝ)*(sp2) + (3868550811269551/50000000000000 : ℝ)*(sp4) + (7737059232481033/100000000000000 : ℝ)*(sp5) + (3868529203525929/50000000000000 : ℝ)*(sp6) + (1973890696958939/50000000000000 : ℝ)*(sp7) + (1973890696958939/50000000000000 : ℝ)*(f.failure) + (3868550811269551/50000000000000 : ℝ)*(f.sum) + (303155917187/344500000000000000000000000 : ℝ)*base65 + (325586251722006409/86125000000000000000000000000000 : ℝ)*base68 + (2119392831745256409/86125000000000000000000000000000 : ℝ)*base70 + (888595947829743591/86125000000000000000000000000000 : ℝ)*base71 + (1055794975739/172250000000000000000000000 : ℝ)*base74 + (1708364223935631409/86125000000000000000000000000000 : ℝ)*base76 + (309920006001993591/86125000000000000000000000000000 : ℝ)*base77 + (488386376213993591/86125000000000000000000000000000 : ℝ)*base79 + (832012440513/344500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (21933341/2500000000000000000000 : ℝ)*base89 + (21933341/2500000000000000000000 : ℝ)*base91 + (21933341/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1066_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2801/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1066_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1066_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1066_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1066_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1066_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4129/1024 : ℝ) ≤ p) (hpb : p ≤ (8259/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73996519/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11251/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14003/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1066_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
