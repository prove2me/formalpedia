-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1392_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:26:20.297735+00:00
-- url     : https://prove2.me/submissions/5dd01429-0766-4c18-9262-47a96a5d4d7d

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
theorem support_rectangle_w1392_s6_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001550133/10000000000 : ℝ)*x 0 + (1352532943/2500000000 : ℝ)*x 1 + (52460139/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001550133/10000000000 : ℝ)^17 ≤ (12201193369271/100000000000000 : ℝ)^13 := by
    have hnat : (2001550133 : ℕ)^17*100000000000000^13 ≤ 12201193369271^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001550133 10000000000 12201193369271 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352532943/2500000000 : ℝ)^17 ≤ (87467756599/195312500000 : ℝ)^13 := by
    have hnat : (1352532943 : ℕ)^17*195312500000^13 ≤ 87467756599^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352532943 2500000000 87467756599 195312500000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52460139/100000000 : ℝ)^17 ≤ (43015315229423/100000000000000 : ℝ)^13 := by
    have hnat : (52460139 : ℕ)^17*100000000000000^13 ≤ 43015315229423^13*100000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52460139 100000000 43015315229423 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001550133/10000000000 : ℝ), (1352532943/2500000000 : ℝ), (52460139/100000000 : ℝ)] ![(12201193369271/100000000000000 : ℝ), (87467756599/195312500000 : ℝ), (43015315229423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001550133/10000000000 : ℝ)|^17 ≤ (12201193369271/100000000000000 : ℝ)^13
        have hw : |(-2001550133/10000000000 : ℝ)|=(2001550133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352532943/2500000000 : ℝ)|^17 ≤ (87467756599/195312500000 : ℝ)^13
        have hw : |(1352532943/2500000000 : ℝ)|=(1352532943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52460139/100000000 : ℝ)|^17 ≤ (43015315229423/100000000000000 : ℝ)^13
        have hw : |(52460139/100000000 : ℝ)|=(52460139/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s6_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5348079151/10000000000 : ℝ)*x 0 + (-104256583/500000000 : ℝ)*x 1 + (2623006961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348079151/10000000000 : ℝ)^17 ≤ (4411297908827/10000000000000 : ℝ)^13 := by
    have hnat : (5348079151 : ℕ)^17*10000000000000^13 ≤ 4411297908827^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348079151 10000000000 4411297908827 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104256583/500000000 : ℝ)^17 ≤ (804481589733/6250000000000 : ℝ)^13 := by
    have hnat : (104256583 : ℕ)^17*6250000000000^13 ≤ 804481589733^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104256583 500000000 804481589733 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623006961/5000000000 : ℝ)^17 ≤ (1075382886633/2500000000000 : ℝ)^13 := by
    have hnat : (2623006961 : ℕ)^17*2500000000000^13 ≤ 1075382886633^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623006961 5000000000 1075382886633 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348079151/10000000000 : ℝ), (-104256583/500000000 : ℝ), (2623006961/5000000000 : ℝ)] ![(4411297908827/10000000000000 : ℝ), (804481589733/6250000000000 : ℝ), (1075382886633/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348079151/10000000000 : ℝ)|^17 ≤ (4411297908827/10000000000000 : ℝ)^13
        have hw : |(5348079151/10000000000 : ℝ)|=(5348079151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104256583/500000000 : ℝ)|^17 ≤ (804481589733/6250000000000 : ℝ)^13
        have hw : |(-104256583/500000000 : ℝ)|=(104256583/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623006961/5000000000 : ℝ)|^17 ≤ (1075382886633/2500000000000 : ℝ)^13
        have hw : |(2623006961/5000000000 : ℝ)|=(2623006961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s6_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5348079221/10000000000 : ℝ)*x 0 + (5246013863/10000000000 : ℝ)*x 1 + (-521282911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348079221/10000000000 : ℝ)^17 ≤ (22056489921657/50000000000000 : ℝ)^13 := by
    have hnat : (5348079221 : ℕ)^17*50000000000000^13 ≤ 22056489921657^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348079221 10000000000 22056489921657 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246013863/10000000000 : ℝ)^17 ≤ (2688457177043/6250000000000 : ℝ)^13 := by
    have hnat : (5246013863 : ℕ)^17*6250000000000^13 ≤ 2688457177043^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246013863 10000000000 2688457177043 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521282911/2500000000 : ℝ)^17 ≤ (1608963163321/12500000000000 : ℝ)^13 := by
    have hnat : (521282911 : ℕ)^17*12500000000000^13 ≤ 1608963163321^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521282911 2500000000 1608963163321 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348079221/10000000000 : ℝ), (5246013863/10000000000 : ℝ), (-521282911/2500000000 : ℝ)] ![(22056489921657/50000000000000 : ℝ), (2688457177043/6250000000000 : ℝ), (1608963163321/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348079221/10000000000 : ℝ)|^17 ≤ (22056489921657/50000000000000 : ℝ)^13
        have hw : |(5348079221/10000000000 : ℝ)|=(5348079221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246013863/10000000000 : ℝ)|^17 ≤ (2688457177043/6250000000000 : ℝ)^13
        have hw : |(5246013863/10000000000 : ℝ)|=(5246013863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521282911/2500000000 : ℝ)|^17 ≤ (1608963163321/12500000000000 : ℝ)^13
        have hw : |(-521282911/2500000000 : ℝ)|=(521282911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s6_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4313712723/10000000000 : ℝ)*x 0 + (2070922257/5000000000 : ℝ)*x 1 + (1123019771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313712723/10000000000 : ℝ)^17 ≤ (3330410356429/10000000000000 : ℝ)^13 := by
    have hnat : (4313712723 : ℕ)^17*10000000000000^13 ≤ 3330410356429^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313712723 10000000000 3330410356429 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070922257/5000000000 : ℝ)^17 ≤ (7894911649351/25000000000000 : ℝ)^13 := by
    have hnat : (2070922257 : ℕ)^17*25000000000000^13 ≤ 7894911649351^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070922257 5000000000 7894911649351 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123019771/2500000000 : ℝ)^17 ≤ (35116249819439/100000000000000 : ℝ)^13 := by
    have hnat : (1123019771 : ℕ)^17*100000000000000^13 ≤ 35116249819439^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123019771 2500000000 35116249819439 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313712723/10000000000 : ℝ), (2070922257/5000000000 : ℝ), (1123019771/2500000000 : ℝ)] ![(3330410356429/10000000000000 : ℝ), (7894911649351/25000000000000 : ℝ), (35116249819439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313712723/10000000000 : ℝ)|^17 ≤ (3330410356429/10000000000000 : ℝ)^13
        have hw : |(4313712723/10000000000 : ℝ)|=(4313712723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070922257/5000000000 : ℝ)|^17 ≤ (7894911649351/25000000000000 : ℝ)^13
        have hw : |(2070922257/5000000000 : ℝ)|=(2070922257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123019771/2500000000 : ℝ)|^17 ≤ (35116249819439/100000000000000 : ℝ)^13
        have hw : |(1123019771/2500000000 : ℝ)|=(1123019771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s6_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1000780879/5000000000 : ℝ)*x 0 + (524660393/1000000000 : ℝ)*x 1 + (676192341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000780879/5000000000 : ℝ)^17 ≤ (12201286038331/100000000000000 : ℝ)^13 := by
    have hnat : (1000780879 : ℕ)^17*100000000000000^13 ≤ 12201286038331^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000780879 5000000000 12201286038331 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524660393/1000000000 : ℝ)^17 ≤ (10755410495499/25000000000000 : ℝ)^13 := by
    have hnat : (524660393 : ℕ)^17*25000000000000^13 ≤ 10755410495499^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524660393 1000000000 10755410495499 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676192341/1250000000 : ℝ)^17 ≤ (11194267991609/25000000000000 : ℝ)^13 := by
    have hnat : (676192341 : ℕ)^17*25000000000000^13 ≤ 11194267991609^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676192341 1250000000 11194267991609 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1000780879/5000000000 : ℝ), (524660393/1000000000 : ℝ), (676192341/1250000000 : ℝ)] ![(12201286038331/100000000000000 : ℝ), (10755410495499/25000000000000 : ℝ), (11194267991609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1000780879/5000000000 : ℝ)|^17 ≤ (12201286038331/100000000000000 : ℝ)^13
        have hw : |(-1000780879/5000000000 : ℝ)|=(1000780879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524660393/1000000000 : ℝ)|^17 ≤ (10755410495499/25000000000000 : ℝ)^13
        have hw : |(524660393/1000000000 : ℝ)|=(524660393/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676192341/1250000000 : ℝ)|^17 ≤ (11194267991609/25000000000000 : ℝ)^13
        have hw : |(676192341/1250000000 : ℝ)|=(676192341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s6_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (530557277/1000000000 : ℝ)*x 0 + (-1921606789/10000000000 : ℝ)*x 1 + (676192341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530557277/1000000000 : ℝ)^17 ≤ (682110194361/1562500000000 : ℝ)^13 := by
    have hnat : (530557277 : ℕ)^17*1562500000000^13 ≤ 682110194361^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530557277 1000000000 682110194361 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1921606789/10000000000 : ℝ)^17 ≤ (1445984447481/12500000000000 : ℝ)^13 := by
    have hnat : (1921606789 : ℕ)^17*12500000000000^13 ≤ 1445984447481^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921606789 10000000000 1445984447481 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676192341/1250000000 : ℝ)^17 ≤ (11194267991609/25000000000000 : ℝ)^13 := by
    have hnat : (676192341 : ℕ)^17*25000000000000^13 ≤ 11194267991609^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676192341 1250000000 11194267991609 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530557277/1000000000 : ℝ), (-1921606789/10000000000 : ℝ), (676192341/1250000000 : ℝ)] ![(682110194361/1562500000000 : ℝ), (1445984447481/12500000000000 : ℝ), (11194267991609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530557277/1000000000 : ℝ)|^17 ≤ (682110194361/1562500000000 : ℝ)^13
        have hw : |(530557277/1000000000 : ℝ)|=(530557277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1921606789/10000000000 : ℝ)|^17 ≤ (1445984447481/12500000000000 : ℝ)^13
        have hw : |(-1921606789/10000000000 : ℝ)|=(1921606789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676192341/1250000000 : ℝ)|^17 ≤ (11194267991609/25000000000000 : ℝ)^13
        have hw : |(676192341/1250000000 : ℝ)|=(676192341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s6_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (165799149/312500000 : ℝ)*x 0 + (540953873/1000000000 : ℝ)*x 1 + (-1921606789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165799149/312500000 : ℝ)^17 ≤ (2728440776099/6250000000000 : ℝ)^13 := by
    have hnat : (165799149 : ℕ)^17*6250000000000^13 ≤ 2728440776099^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165799149 312500000 2728440776099 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540953873/1000000000 : ℝ)^17 ≤ (8955414397617/20000000000000 : ℝ)^13 := by
    have hnat : (540953873 : ℕ)^17*20000000000000^13 ≤ 8955414397617^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540953873 1000000000 8955414397617 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921606789/10000000000 : ℝ)^17 ≤ (1445984447481/12500000000000 : ℝ)^13 := by
    have hnat : (1921606789 : ℕ)^17*12500000000000^13 ≤ 1445984447481^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921606789 10000000000 1445984447481 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165799149/312500000 : ℝ), (540953873/1000000000 : ℝ), (-1921606789/10000000000 : ℝ)] ![(2728440776099/6250000000000 : ℝ), (8955414397617/20000000000000 : ℝ), (1445984447481/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165799149/312500000 : ℝ)|^17 ≤ (2728440776099/6250000000000 : ℝ)^13
        have hw : |(165799149/312500000 : ℝ)|=(165799149/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540953873/1000000000 : ℝ)|^17 ≤ (8955414397617/20000000000000 : ℝ)^13
        have hw : |(540953873/1000000000 : ℝ)|=(540953873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1921606789/10000000000 : ℝ)|^17 ≤ (1445984447481/12500000000000 : ℝ)^13
        have hw : |(-1921606789/10000000000 : ℝ)|=(1921606789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s6_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4313737517/10000000000 : ℝ)*x 0 + (1122705003/2500000000 : ℝ)*x 1 + (64736097/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313737517/10000000000 : ℝ)^17 ≤ (8326088471581/25000000000000 : ℝ)^13 := by
    have hnat : (4313737517 : ℕ)^17*25000000000000^13 ≤ 8326088471581^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313737517 10000000000 8326088471581 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122705003/2500000000 : ℝ)^17 ≤ (17551689619361/50000000000000 : ℝ)^13 := by
    have hnat : (1122705003 : ℕ)^17*50000000000000^13 ≤ 17551689619361^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122705003 2500000000 17551689619361 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (64736097/156250000 : ℝ)^17 ≤ (3949033356733/12500000000000 : ℝ)^13 := by
    have hnat : (64736097 : ℕ)^17*12500000000000^13 ≤ 3949033356733^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64736097 156250000 3949033356733 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313737517/10000000000 : ℝ), (1122705003/2500000000 : ℝ), (64736097/156250000 : ℝ)] ![(8326088471581/25000000000000 : ℝ), (17551689619361/50000000000000 : ℝ), (3949033356733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313737517/10000000000 : ℝ)|^17 ≤ (8326088471581/25000000000000 : ℝ)^13
        have hw : |(4313737517/10000000000 : ℝ)|=(4313737517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122705003/2500000000 : ℝ)|^17 ≤ (17551689619361/50000000000000 : ℝ)^13
        have hw : |(1122705003/2500000000 : ℝ)|=(1122705003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(64736097/156250000 : ℝ)|^17 ≤ (3949033356733/12500000000000 : ℝ)^13
        have hw : |(64736097/156250000 : ℝ)|=(64736097/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5631/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14737/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11257/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7371/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11257/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7371/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11257/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11257/100000 : ℝ) ^ (4351/1024 : ℝ) ≤ (186424364625161/2000000000000000000 : ℝ) := by
    have hpowers : (11257/100000 : ℝ)^4351 ≤ (186424364625161/2000000000000000000 : ℝ)^1024 := by
      have hnat : (11257 : ℕ)^4351*2000000000000000000^1024 ≤ 186424364625161^1024*100000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11257 100000 186424364625161 2000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11257/100000 : ℝ)) (X := (186424364625161/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7371/50000 : ℝ) ^ (4351/1024 : ℝ) ≤ (14660429375756183/50000000000000000000 : ℝ) := by
    have hpowers : (7371/50000 : ℝ)^4351 ≤ (14660429375756183/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7371 : ℕ)^4351*50000000000000000000^1024 ≤ 14660429375756183^1024*50000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7371 50000 14660429375756183 50000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7371/50000 : ℝ)) (X := (14660429375756183/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000186424364625161/1000000000000000000 : ℝ) ≤ (200008774302211/200000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (1000186424364625161/1000000000000000000 : ℝ)^1024 ≤ (200008774302211/200000000000000 : ℝ)^4351 := by
      have hnat : (1000186424364625161 : ℕ)^1024*200000000000000^4351 ≤ 200008774302211^4351*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000186424364625161 1000000000000000000 200008774302211 200000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200008774302211/200000000000000 : ℝ)) (X := (1000186424364625161/1000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252415129811423151/6250000000000000000 : ℝ) ≤ (10000909299981969/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (6252415129811423151/6250000000000000000 : ℝ)^1024 ≤ (10000909299981969/10000000000000000 : ℝ)^4351 := by
      have hnat : (6252415129811423151 : ℕ)^1024*10000000000000000^4351 ≤ 10000909299981969^4351*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252415129811423151 6250000000000000000 10000909299981969 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000909299981969/10000000000000000 : ℝ)) (X := (6252415129811423151/6250000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014660429375756183/25000000000000000000 : ℝ) ≤ (2500344971213347/2500000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (25014660429375756183/25000000000000000000 : ℝ)^1024 ≤ (2500344971213347/2500000000000000 : ℝ)^4351 := by
      have hnat : (25014660429375756183 : ℕ)^1024*2500000000000000^4351 ≤ 2500344971213347^4351*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014660429375756183 25000000000000000000 2500344971213347 2500000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500344971213347/2500000000000000 : ℝ)) (X := (25014660429375756183/25000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(186424364625161/2000000000000000000 : ℝ) ≤ ((4355116771795642423/4356250000000000000 : ℝ)+2*(470584871419/348500000000000 : ℝ)*(11257/100000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (4355116771795642423/4356250000000000000 : ℝ)+2*(470584871419/348500000000000 : ℝ)*(11257/100000 : ℝ)=(200008774302211/200000000000000 : ℝ) by norm_num, show 1+2*(186424364625161/2000000000000000000 : ℝ)=(1000186424364625161/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14660429375756183/50000000000000000000 : ℝ)+(186424364625161/2000000000000000000 : ℝ) ≤ ((4355116771795642423/4356250000000000000 : ℝ)+(470584871419/348500000000000 : ℝ)*((7371/50000 : ℝ)+(11257/100000 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (4355116771795642423/4356250000000000000 : ℝ)+(470584871419/348500000000000 : ℝ)*((7371/50000 : ℝ)+(11257/100000 : ℝ))=(10000909299981969/10000000000000000 : ℝ) by norm_num, show 1+(14660429375756183/50000000000000000000 : ℝ)+(186424364625161/2000000000000000000 : ℝ)=(6252415129811423151/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14660429375756183/50000000000000000000 : ℝ) ≤ ((4355116771795642423/4356250000000000000 : ℝ)+2*(470584871419/348500000000000 : ℝ)*(7371/50000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (4355116771795642423/4356250000000000000 : ℝ)+2*(470584871419/348500000000000 : ℝ)*(7371/50000 : ℝ)=(2500344971213347/2500000000000000 : ℝ) by norm_num, show 1+2*(14660429375756183/50000000000000000000 : ℝ)=(25014660429375756183/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4355116771795642423/4356250000000000000 : ℝ)*(X 1 0+X 2 0)+(470584871419/348500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (4355116771795642423/4356250000000000000 : ℝ)) (alpha := (470584871419/348500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4355116771795642423/4356250000000000000 : ℝ)*(X 0 1+X 2 1)+(470584871419/348500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (4355116771795642423/4356250000000000000 : ℝ)) (alpha := (470584871419/348500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4355116771795642423/4356250000000000000 : ℝ)*(X 0 2+X 1 2)+(470584871419/348500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (11257/100000 : ℝ)) (hi := (7371/50000 : ℝ)) (c := (4355116771795642423/4356250000000000000 : ℝ)) (alpha := (470584871419/348500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2001550133/10000000000 : ℝ)*X 0 0+(1352532943/2500000000 : ℝ)*X 0 1+(52460139/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348079151/10000000000 : ℝ)*X 1 0+(-104256583/500000000 : ℝ)*X 1 1+(2623006961/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348079221/10000000000 : ℝ)*X 2 0+(5246013863/10000000000 : ℝ)*X 2 1+(-521282911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313712723/10000000000 : ℝ)*X 0 0+(2070922257/5000000000 : ℝ)*X 0 1+(1123019771/2500000000 : ℝ)*X 0 2+(4313712723/10000000000 : ℝ)*X 1 0+(2070922257/5000000000 : ℝ)*X 1 1+(1123019771/2500000000 : ℝ)*X 1 2+(4313712723/10000000000 : ℝ)*X 2 0+(2070922257/5000000000 : ℝ)*X 2 1+(1123019771/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1000780879/5000000000 : ℝ)*X 0 0+(524660393/1000000000 : ℝ)*X 0 1+(676192341/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530557277/1000000000 : ℝ)*X 1 0+(-1921606789/10000000000 : ℝ)*X 1 1+(676192341/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165799149/312500000 : ℝ)*X 2 0+(540953873/1000000000 : ℝ)*X 2 1+(-1921606789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313737517/10000000000 : ℝ)*X 0 0+(1122705003/2500000000 : ℝ)*X 0 1+(64736097/156250000 : ℝ)*X 0 2+(4313737517/10000000000 : ℝ)*X 1 0+(1122705003/2500000000 : ℝ)*X 1 1+(64736097/156250000 : ℝ)*X 1 2+(4313737517/10000000000 : ℝ)*X 2 0+(1122705003/2500000000 : ℝ)*X 2 1+(64736097/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81246959731411620984567/17425000000000000000000000000 : ℝ) := by norm_num
    linear_combination (451444161/50000000000000 : ℝ)*(base19) + (183040491/20000000000000 : ℝ)*(base23) + (4508353/12500000000000 : ℝ)*(lower2) + (13485897/10000000000000 : ℝ)*(upper3) + (29691949/25000000000000 : ℝ)*(upper5) + (279639539912491/6250000000000 : ℝ)*(major0) + (279639539912491/6250000000000 : ℝ)*(major1) + (279639539912491/6250000000000 : ℝ)*(major2) + (1523299861314769/25000000000000 : ℝ)*(sp0) + (6093217363852897/100000000000000 : ℝ)*(sp1) + (1218643470307753/20000000000000 : ℝ)*(sp2) + (285523762994969/10000000000000 : ℝ)*(sp3) + (18821482143/100000000000000 : ℝ)*(sp4) + (4612543293/50000000000000 : ℝ)*(sp7) + (713811713759069/25000000000000 : ℝ)*(f.failure) + (6093218266741219/100000000000000 : ℝ)*(f.sum) + (63117774117293/8712500000000000000000000000 : ℝ)*base66 + (3088231457711251/400390625000000000000000000000 : ℝ)*base67 + (13304425728451871/1601562500000000000000000000000 : ℝ)*base70 + (36599826980049383/3203125000000000000000000000000 : ℝ)*base71 + (563546137879/1089062500000000000000000000 : ℝ)*base73 + (719392330619219/100097656250000000000000000000 : ℝ)*base75 + (33855635233856867/3203125000000000000000000000000 : ℝ)*base78 + (19639218326825617/3203125000000000000000000000000 : ℝ)*base80 + (16133257077559/4356250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1911697/250000000000000000000 : ℝ)*base89 + (1911697/250000000000000000000 : ℝ)*base91 + (1911697/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (947436857987013550277824623/217812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (747309641/100000000000000 : ℝ)*(base19) + (405529673/50000000000000 : ℝ)*(base23) + (17791653/20000000000000 : ℝ)*(upper3) + (1495879/5000000000000 : ℝ)*(lower4) + (5551279/6250000000000 : ℝ)*(upper5) + (4506692554185467/100000000000000 : ℝ)*(major0) + (4506692554185467/100000000000000 : ℝ)*(major1) + (4506692554185467/100000000000000 : ℝ)*(major2) + (3884599181/25000000000000 : ℝ)*(sp1) + (8372949403/50000000000000 : ℝ)*(sp2) + (1227484740447101/20000000000000 : ℝ)*(sp4) + (6137407416529139/100000000000000 : ℝ)*(sp5) + (6137406145277353/100000000000000 : ℝ)*(sp6) + (359495157642837/12500000000000 : ℝ)*(sp7) + (359495157642837/12500000000000 : ℝ)*(f.failure) + (1227484740447101/20000000000000 : ℝ)*(f.sum) + (54498175835823/17425000000000000000000000000 : ℝ)*base65 + (16206796109113473/25625000000000000000000000000000 : ℝ)*base67 + (254229496169636527/25625000000000000000000000000000 : ℝ)*base70 + (114432413269113473/25625000000000000000000000000000 : ℝ)*base71 + (2662687273531/2178125000000000000000000000 : ℝ)*base73 + (252949503844636527/25625000000000000000000000000000 : ℝ)*base76 + (137722375428386527/25625000000000000000000000000000 : ℝ)*base78 + (34991815977136527/25625000000000000000000000000000 : ℝ)*base80 + (9744227879599/8712500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (35719/125000000000000000000 : ℝ)*base90 + (35719/125000000000000000000 : ℝ)*base92 + (35719/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1392_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1392_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1392_s7_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-15637139/78125000 : ℝ)*x 0 + (5410093709/10000000000 : ℝ)*x 1 + (5246049607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15637139/78125000 : ℝ)^17 ≤ (12201222537089/100000000000000 : ℝ)^13 := by
    have hnat : (15637139 : ℕ)^17*100000000000000^13 ≤ 12201222537089^13*78125000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15637139 78125000 12201222537089 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410093709/10000000000 : ℝ)^17 ≤ (22391539679381/50000000000000 : ℝ)^13 := by
    have hnat : (5410093709 : ℕ)^17*50000000000000^13 ≤ 22391539679381^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410093709 10000000000 22391539679381 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246049607/10000000000 : ℝ)^17 ≤ (21507849050471/50000000000000 : ℝ)^13 := by
    have hnat : (5246049607 : ℕ)^17*50000000000000^13 ≤ 21507849050471^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246049607 10000000000 21507849050471 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15637139/78125000 : ℝ), (5410093709/10000000000 : ℝ), (5246049607/10000000000 : ℝ)] ![(12201222537089/100000000000000 : ℝ), (22391539679381/50000000000000 : ℝ), (21507849050471/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15637139/78125000 : ℝ)|^17 ≤ (12201222537089/100000000000000 : ℝ)^13
        have hw : |(-15637139/78125000 : ℝ)|=(15637139/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410093709/10000000000 : ℝ)|^17 ≤ (22391539679381/50000000000000 : ℝ)^13
        have hw : |(5410093709/10000000000 : ℝ)|=(5410093709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246049607/10000000000 : ℝ)|^17 ≤ (21507849050471/50000000000000 : ℝ)^13
        have hw : |(5246049607/10000000000 : ℝ)|=(5246049607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s7_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1069613913/2000000000 : ℝ)*x 0 + (-1042548467/5000000000 : ℝ)*x 1 + (1311512427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069613913/2000000000 : ℝ)^17 ≤ (44112875690437/100000000000000 : ℝ)^13 := by
    have hnat : (1069613913 : ℕ)^17*100000000000000^13 ≤ 44112875690437^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069613913 2000000000 44112875690437 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042548467/5000000000 : ℝ)^17 ≤ (1287142511073/10000000000000 : ℝ)^13 := by
    have hnat : (1042548467 : ℕ)^17*10000000000000^13 ≤ 1287142511073^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042548467 5000000000 1287142511073 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311512427/2500000000 : ℝ)^17 ≤ (10753924795981/25000000000000 : ℝ)^13 := by
    have hnat : (1311512427 : ℕ)^17*25000000000000^13 ≤ 10753924795981^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311512427 2500000000 10753924795981 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069613913/2000000000 : ℝ), (-1042548467/5000000000 : ℝ), (1311512427/2500000000 : ℝ)] ![(44112875690437/100000000000000 : ℝ), (1287142511073/10000000000000 : ℝ), (10753924795981/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069613913/2000000000 : ℝ)|^17 ≤ (44112875690437/100000000000000 : ℝ)^13
        have hw : |(1069613913/2000000000 : ℝ)|=(1069613913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042548467/5000000000 : ℝ)|^17 ≤ (1287142511073/10000000000000 : ℝ)^13
        have hw : |(-1042548467/5000000000 : ℝ)|=(1042548467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311512427/2500000000 : ℝ)|^17 ≤ (10753924795981/25000000000000 : ℝ)^13
        have hw : |(1311512427/2500000000 : ℝ)|=(1311512427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s7_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2674034739/5000000000 : ℝ)*x 0 + (5246049787/10000000000 : ℝ)*x 1 + (-417019389/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674034739/5000000000 : ℝ)^17 ≤ (22056437376013/50000000000000 : ℝ)^13 := by
    have hnat : (2674034739 : ℕ)^17*50000000000000^13 ≤ 22056437376013^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674034739 5000000000 22056437376013 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246049787/10000000000 : ℝ)^17 ≤ (4301570003101/10000000000000 : ℝ)^13 := by
    have hnat : (5246049787 : ℕ)^17*10000000000000^13 ≤ 4301570003101^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246049787 10000000000 4301570003101 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417019389/2000000000 : ℝ)^17 ≤ (12871425199527/100000000000000 : ℝ)^13 := by
    have hnat : (417019389 : ℕ)^17*100000000000000^13 ≤ 12871425199527^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417019389 2000000000 12871425199527 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674034739/5000000000 : ℝ), (5246049787/10000000000 : ℝ), (-417019389/2000000000 : ℝ)] ![(22056437376013/50000000000000 : ℝ), (4301570003101/10000000000000 : ℝ), (12871425199527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674034739/5000000000 : ℝ)|^17 ≤ (22056437376013/50000000000000 : ℝ)^13
        have hw : |(2674034739/5000000000 : ℝ)|=(2674034739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246049787/10000000000 : ℝ)|^17 ≤ (4301570003101/10000000000000 : ℝ)^13
        have hw : |(5246049787/10000000000 : ℝ)|=(5246049787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417019389/2000000000 : ℝ)|^17 ≤ (12871425199527/100000000000000 : ℝ)^13
        have hw : |(-417019389/2000000000 : ℝ)|=(417019389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s7_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4313715303/10000000000 : ℝ)*x 0 + (2070961541/5000000000 : ℝ)*x 1 + (898399981/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313715303/10000000000 : ℝ)^17 ≤ (16652064806069/50000000000000 : ℝ)^13 := by
    have hnat : (4313715303 : ℕ)^17*50000000000000^13 ≤ 16652064806069^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313715303 10000000000 16652064806069 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070961541/5000000000 : ℝ)^17 ≤ (7895107491433/25000000000000 : ℝ)^13 := by
    have hnat : (2070961541 : ℕ)^17*25000000000000^13 ≤ 7895107491433^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070961541 5000000000 7895107491433 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898399981/2000000000 : ℝ)^17 ≤ (17557720198593/50000000000000 : ℝ)^13 := by
    have hnat : (898399981 : ℕ)^17*50000000000000^13 ≤ 17557720198593^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898399981 2000000000 17557720198593 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313715303/10000000000 : ℝ), (2070961541/5000000000 : ℝ), (898399981/2000000000 : ℝ)] ![(16652064806069/50000000000000 : ℝ), (7895107491433/25000000000000 : ℝ), (17557720198593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313715303/10000000000 : ℝ)|^17 ≤ (16652064806069/50000000000000 : ℝ)^13
        have hw : |(4313715303/10000000000 : ℝ)|=(4313715303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070961541/5000000000 : ℝ)|^17 ≤ (7895107491433/25000000000000 : ℝ)^13
        have hw : |(2070961541/5000000000 : ℝ)|=(2070961541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898399981/2000000000 : ℝ)|^17 ≤ (17557720198593/50000000000000 : ℝ)^13
        have hw : |(898399981/2000000000 : ℝ)|=(898399981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s7_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001565391/10000000000 : ℝ)*x 0 + (524663919/1000000000 : ℝ)*x 1 + (5409501123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001565391/10000000000 : ℝ)^17 ≤ (12201314998941/100000000000000 : ℝ)^13 := by
    have hnat : (2001565391 : ℕ)^17*100000000000000^13 ≤ 12201314998941^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001565391 10000000000 12201314998941 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524663919/1000000000 : ℝ)^17 ≤ (8604404014719/20000000000000 : ℝ)^13 := by
    have hnat : (524663919 : ℕ)^17*20000000000000^13 ≤ 8604404014719^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524663919 1000000000 8604404014719 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409501123/10000000000 : ℝ)^17 ≤ (2238833245897/5000000000000 : ℝ)^13 := by
    have hnat : (5409501123 : ℕ)^17*5000000000000^13 ≤ 2238833245897^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409501123 10000000000 2238833245897 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001565391/10000000000 : ℝ), (524663919/1000000000 : ℝ), (5409501123/10000000000 : ℝ)] ![(12201314998941/100000000000000 : ℝ), (8604404014719/20000000000000 : ℝ), (2238833245897/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001565391/10000000000 : ℝ)|^17 ≤ (12201314998941/100000000000000 : ℝ)^13
        have hw : |(-2001565391/10000000000 : ℝ)|=(2001565391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524663919/1000000000 : ℝ)|^17 ≤ (8604404014719/20000000000000 : ℝ)^13
        have hw : |(524663919/1000000000 : ℝ)|=(524663919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409501123/10000000000 : ℝ)|^17 ≤ (2238833245897/5000000000000 : ℝ)^13
        have hw : |(5409501123/10000000000 : ℝ)|=(5409501123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s7_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5305582297/10000000000 : ℝ)*x 0 + (-960822747/5000000000 : ℝ)*x 1 + (5409501109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305582297/10000000000 : ℝ)^17 ≤ (43655154948599/100000000000000 : ℝ)^13 := by
    have hnat : (5305582297 : ℕ)^17*100000000000000^13 ≤ 43655154948599^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305582297 10000000000 43655154948599 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (960822747/5000000000 : ℝ)^17 ≤ (2313636054653/20000000000000 : ℝ)^13 := by
    have hnat : (960822747 : ℕ)^17*20000000000000^13 ≤ 2313636054653^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960822747 5000000000 2313636054653 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409501109/10000000000 : ℝ)^17 ≤ (27985415479/62500000000 : ℝ)^13 := by
    have hnat : (5409501109 : ℕ)^17*62500000000^13 ≤ 27985415479^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409501109 10000000000 27985415479 62500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305582297/10000000000 : ℝ), (-960822747/5000000000 : ℝ), (5409501109/10000000000 : ℝ)] ![(43655154948599/100000000000000 : ℝ), (2313636054653/20000000000000 : ℝ), (27985415479/62500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305582297/10000000000 : ℝ)|^17 ≤ (43655154948599/100000000000000 : ℝ)^13
        have hw : |(5305582297/10000000000 : ℝ)|=(5305582297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-960822747/5000000000 : ℝ)|^17 ≤ (2313636054653/20000000000000 : ℝ)^13
        have hw : |(-960822747/5000000000 : ℝ)|=(960822747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409501109/10000000000 : ℝ)|^17 ≤ (27985415479/62500000000 : ℝ)^13
        have hw : |(5409501109/10000000000 : ℝ)|=(5409501109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s7_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5305582307/10000000000 : ℝ)*x 0 + (1081900217/2000000000 : ℝ)*x 1 + (-960822757/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305582307/10000000000 : ℝ)^17 ≤ (21827577528099/50000000000000 : ℝ)^13 := by
    have hnat : (5305582307 : ℕ)^17*50000000000000^13 ≤ 21827577528099^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305582307 10000000000 21827577528099 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081900217/2000000000 : ℝ)^17 ≤ (44776664506617/100000000000000 : ℝ)^13 := by
    have hnat : (1081900217 : ℕ)^17*100000000000000^13 ≤ 44776664506617^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081900217 2000000000 44776664506617 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960822757/5000000000 : ℝ)^17 ≤ (1156818043071/10000000000000 : ℝ)^13 := by
    have hnat : (960822757 : ℕ)^17*10000000000000^13 ≤ 1156818043071^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960822757 5000000000 1156818043071 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305582307/10000000000 : ℝ), (1081900217/2000000000 : ℝ), (-960822757/5000000000 : ℝ)] ![(21827577528099/50000000000000 : ℝ), (44776664506617/100000000000000 : ℝ), (1156818043071/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305582307/10000000000 : ℝ)|^17 ≤ (21827577528099/50000000000000 : ℝ)^13
        have hw : |(5305582307/10000000000 : ℝ)|=(5305582307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1081900217/2000000000 : ℝ)|^17 ≤ (44776664506617/100000000000000 : ℝ)^13
        have hw : |(1081900217/2000000000 : ℝ)|=(1081900217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-960822757/5000000000 : ℝ)|^17 ≤ (1156818043071/10000000000000 : ℝ)^13
        have hw : |(-960822757/5000000000 : ℝ)|=(960822757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_s7_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4313740103/10000000000 : ℝ)*x 0 + (2245370961/5000000000 : ℝ)*x 1 + (4143187641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4313740103/10000000000 : ℝ)^17 ≤ (16652189997397/50000000000000 : ℝ)^13 := by
    have hnat : (4313740103 : ℕ)^17*50000000000000^13 ≤ 16652189997397^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313740103 10000000000 16652189997397 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245370961/5000000000 : ℝ)^17 ≤ (175512905089/500000000000 : ℝ)^13 := by
    have hnat : (2245370961 : ℕ)^17*500000000000^13 ≤ 175512905089^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245370961 5000000000 175512905089 500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4143187641/10000000000 : ℝ)^17 ≤ (31593038978139/100000000000000 : ℝ)^13 := by
    have hnat : (4143187641 : ℕ)^17*100000000000000^13 ≤ 31593038978139^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143187641 10000000000 31593038978139 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4313740103/10000000000 : ℝ), (2245370961/5000000000 : ℝ), (4143187641/10000000000 : ℝ)] ![(16652189997397/50000000000000 : ℝ), (175512905089/500000000000 : ℝ), (31593038978139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4313740103/10000000000 : ℝ)|^17 ≤ (16652189997397/50000000000000 : ℝ)^13
        have hw : |(4313740103/10000000000 : ℝ)|=(4313740103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245370961/5000000000 : ℝ)|^17 ≤ (175512905089/500000000000 : ℝ)^13
        have hw : |(2245370961/5000000000 : ℝ)|=(2245370961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4143187641/10000000000 : ℝ)|^17 ≤ (31593038978139/100000000000000 : ℝ)^13
        have hw : |(4143187641/10000000000 : ℝ)|=(4143187641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11263/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (921/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5631/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5631/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5631/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5631/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5631/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5631/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5631/50000 : ℝ) ^ (4351/1024 : ℝ) ≤ (1167352835353151/12500000000000000000 : ℝ) := by
    have hpowers : (5631/50000 : ℝ)^4351 ≤ (1167352835353151/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5631 : ℕ)^4351*12500000000000000000^1024 ≤ 1167352835353151^1024*50000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5631 50000 1167352835353151 12500000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5631/50000 : ℝ)) (X := (1167352835353151/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14737/100000 : ℝ) ^ (4351/1024 : ℝ) ≤ (29278626900492853/100000000000000000000 : ℝ) := by
    have hpowers : (14737/100000 : ℝ)^4351 ≤ (29278626900492853/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14737 : ℕ)^4351*100000000000000000000^1024 ≤ 29278626900492853^1024*100000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14737 100000 29278626900492853 100000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14737/100000 : ℝ)) (X := (29278626900492853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251167352835353151/6250000000000000000 : ℝ) ≤ (10000439543627519/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (6251167352835353151/6250000000000000000 : ℝ)^1024 ≤ (10000439543627519/10000000000000000 : ℝ)^4351 := by
      have hnat : (6251167352835353151 : ℕ)^1024*10000000000000000^4351 ≤ 10000439543627519^4351*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251167352835353151 6250000000000000000 10000439543627519 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000439543627519/10000000000000000 : ℝ)) (X := (6251167352835353151/6250000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038617449583318061/100000000000000000000 : ℝ) ≤ (312528397517241/312500000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (100038617449583318061/100000000000000000000 : ℝ)^1024 ≤ (312528397517241/312500000000000 : ℝ)^4351 := by
      have hnat : (100038617449583318061 : ℕ)^1024*312500000000000^4351 ≤ 312528397517241^4351*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038617449583318061 100000000000000000000 312528397517241 312500000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312528397517241/312500000000000 : ℝ)) (X := (100038617449583318061/100000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029278626900492853/50000000000000000000 : ℝ) ≤ (2000275579495181/2000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (50029278626900492853/50000000000000000000 : ℝ)^1024 ≤ (2000275579495181/2000000000000000 : ℝ)^4351 := by
      have hnat : (50029278626900492853 : ℕ)^1024*2000000000000000^4351 ≤ 2000275579495181^4351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029278626900492853 50000000000000000000 2000275579495181 2000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000275579495181/2000000000000000 : ℝ)) (X := (50029278626900492853/50000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1167352835353151/12500000000000000000 : ℝ) ≤ ((34740959673065105393/34750000000000000000 : ℝ)+2*(469176924193/347500000000000 : ℝ)*(5631/50000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (34740959673065105393/34750000000000000000 : ℝ)+2*(469176924193/347500000000000 : ℝ)*(5631/50000 : ℝ)=(10000439543627519/10000000000000000 : ℝ) by norm_num, show 1+2*(1167352835353151/12500000000000000000 : ℝ)=(6251167352835353151/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29278626900492853/100000000000000000000 : ℝ)+(1167352835353151/12500000000000000000 : ℝ) ≤ ((34740959673065105393/34750000000000000000 : ℝ)+(469176924193/347500000000000 : ℝ)*((14737/100000 : ℝ)+(5631/50000 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (34740959673065105393/34750000000000000000 : ℝ)+(469176924193/347500000000000 : ℝ)*((14737/100000 : ℝ)+(5631/50000 : ℝ))=(312528397517241/312500000000000 : ℝ) by norm_num, show 1+(29278626900492853/100000000000000000000 : ℝ)+(1167352835353151/12500000000000000000 : ℝ)=(100038617449583318061/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29278626900492853/100000000000000000000 : ℝ) ≤ ((34740959673065105393/34750000000000000000 : ℝ)+2*(469176924193/347500000000000 : ℝ)*(14737/100000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (34740959673065105393/34750000000000000000 : ℝ)+2*(469176924193/347500000000000 : ℝ)*(14737/100000 : ℝ)=(2000275579495181/2000000000000000 : ℝ) by norm_num, show 1+2*(29278626900492853/100000000000000000000 : ℝ)=(50029278626900492853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34740959673065105393/34750000000000000000 : ℝ)*(X 1 0+X 2 0)+(469176924193/347500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (34740959673065105393/34750000000000000000 : ℝ)) (alpha := (469176924193/347500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34740959673065105393/34750000000000000000 : ℝ)*(X 0 1+X 2 1)+(469176924193/347500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (34740959673065105393/34750000000000000000 : ℝ)) (alpha := (469176924193/347500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34740959673065105393/34750000000000000000 : ℝ)*(X 0 2+X 1 2)+(469176924193/347500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (5631/50000 : ℝ)) (hi := (14737/100000 : ℝ)) (c := (34740959673065105393/34750000000000000000 : ℝ)) (alpha := (469176924193/347500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-15637139/78125000 : ℝ)*X 0 0+(5410093709/10000000000 : ℝ)*X 0 1+(5246049607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069613913/2000000000 : ℝ)*X 1 0+(-1042548467/5000000000 : ℝ)*X 1 1+(1311512427/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674034739/5000000000 : ℝ)*X 2 0+(5246049787/10000000000 : ℝ)*X 2 1+(-417019389/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4313715303/10000000000 : ℝ)*X 0 0+(2070961541/5000000000 : ℝ)*X 0 1+(898399981/2000000000 : ℝ)*X 0 2+(4313715303/10000000000 : ℝ)*X 1 0+(2070961541/5000000000 : ℝ)*X 1 1+(898399981/2000000000 : ℝ)*X 1 2+(4313715303/10000000000 : ℝ)*X 2 0+(2070961541/5000000000 : ℝ)*X 2 1+(898399981/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2001565391/10000000000 : ℝ)*X 0 0+(524663919/1000000000 : ℝ)*X 0 1+(5409501123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305582297/10000000000 : ℝ)*X 1 0+(-960822747/5000000000 : ℝ)*X 1 1+(5409501109/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305582307/10000000000 : ℝ)*X 2 0+(1081900217/2000000000 : ℝ)*X 2 1+(-960822757/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4313740103/10000000000 : ℝ)*X 0 0+(2245370961/5000000000 : ℝ)*X 0 1+(4143187641/10000000000 : ℝ)*X 0 2+(4313740103/10000000000 : ℝ)*X 1 0+(2245370961/5000000000 : ℝ)*X 1 1+(4143187641/10000000000 : ℝ)*X 1 2+(4313740103/10000000000 : ℝ)*X 2 0+(2245370961/5000000000 : ℝ)*X 2 1+(4143187641/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1097427148743465279210741111/434375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (501733153/100000000000000 : ℝ)*(base19) + (189096639/50000000000000 : ℝ)*(base23) + (325881/2500000000000 : ℝ)*(lower2) + (6517479/6250000000000 : ℝ)*(upper3) + (55525769/100000000000000 : ℝ)*(upper5) + (2238118471760491/50000000000000 : ℝ)*(major0) + (2238118471760491/50000000000000 : ℝ)*(major1) + (2238118471760491/50000000000000 : ℝ)*(major2) + (761991989250147/12500000000000 : ℝ)*(sp0) + (1219189478403933/20000000000000 : ℝ)*(sp1) + (304797375777977/5000000000000 : ℝ)*(sp2) + (22316567476631/781250000000 : ℝ)*(sp3) + (5989875821/50000000000000 : ℝ)*(sp4) + (2636032667/50000000000000 : ℝ)*(sp7) + (1428262954537051/50000000000000 : ℝ)*(f.failure) + (3047973946876409/50000000000000 : ℝ)*(f.sum) + (38605907552987/8687500000000000000000000000 : ℝ)*base66 + (23127285294644727963/1737500000000000000000000000000000 : ℝ)*base67 + (16026349983194727963/1737500000000000000000000000000000 : ℝ)*base69 + (29759504983682227963/1737500000000000000000000000000000 : ℝ)*base71 + (13221642662319/4343750000000000000000000000 : ℝ)*base73 + (17258105394969727963/1737500000000000000000000000000000 : ℝ)*base75 + (9434708847369727963/1737500000000000000000000000000000 : ℝ)*base77 + (3495673505655272037/1737500000000000000000000000000000 : ℝ)*base80 + (2439103334597/2171875000000000000000000000 : ℝ)*base81 + (4438137/500000000000000000000 : ℝ)*base90 + (4438137/500000000000000000000 : ℝ)*base92 + (4438137/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3853018067885589166510817403/1737500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53176877/12500000000000 : ℝ)*(base19) + (483831143/100000000000000 : ℝ)*(base23) + (145465167/100000000000000 : ℝ)*(lower1) + (8245063/20000000000000 : ℝ)*(upper3) + (12269833/50000000000000 : ℝ)*(lower4) + (12021679/25000000000000 : ℝ)*(upper5) + (4508702563188857/100000000000000 : ℝ)*(major0) + (4508702563188857/100000000000000 : ℝ)*(major1) + (4508702563188857/100000000000000 : ℝ)*(major2) + (18436919/25000000000000 : ℝ)*(sp2) + (1535040274299689/25000000000000 : ℝ)*(sp4) + (307008033589187/5000000000000 : ℝ)*(sp5) + (6140160539619937/100000000000000 : ℝ)*(sp6) + (1438621977630061/50000000000000 : ℝ)*(sp7) + (1438621977630061/50000000000000 : ℝ)*(f.failure) + (1535040274299689/25000000000000 : ℝ)*(f.sum) + (108399523286349/17375000000000000000000000000 : ℝ)*base66 + (250640365529708305801/3475000000000000000000000000000000 : ℝ)*base67 + (19065410874641694199/3475000000000000000000000000000000 : ℝ)*base70 + (85625329783258305801/3475000000000000000000000000000000 : ℝ)*base71 + (45094543987099/17375000000000000000000000000 : ℝ)*base74 + (310277238109841694199/3475000000000000000000000000000000 : ℝ)*base76 + (8144893816066694199/3475000000000000000000000000000000 : ℝ)*base78 + (69795740304366694199/3475000000000000000000000000000000 : ℝ)*base80 + (113105903332099/17375000000000000000000000000 : ℝ)*base82 + (6072993/500000000000000000000 : ℝ)*base89 + (6072993/500000000000000000000 : ℝ)*base91 + (6072993/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1392_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5631/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (921/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1392_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1392_box_0 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1838171601/10000000000 : ℝ)*x 0 + (2693915927/5000000000 : ℝ)*x 1 + (2693915873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1838171601/10000000000 : ℝ)^17 ≤ (5457745789887/50000000000000 : ℝ)^13 := by
    have hnat : (1838171601 : ℕ)^17*50000000000000^13 ≤ 5457745789887^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838171601 10000000000 5457745789887 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693915927/5000000000 : ℝ)^17 ≤ (11135563696009/25000000000000 : ℝ)^13 := by
    have hnat : (2693915927 : ℕ)^17*25000000000000^13 ≤ 11135563696009^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693915927 5000000000 11135563696009 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2693915873/5000000000 : ℝ)^17 ≤ (22271126808227/50000000000000 : ℝ)^13 := by
    have hnat : (2693915873 : ℕ)^17*50000000000000^13 ≤ 22271126808227^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693915873 5000000000 22271126808227 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1838171601/10000000000 : ℝ), (2693915927/5000000000 : ℝ), (2693915873/5000000000 : ℝ)] ![(5457745789887/50000000000000 : ℝ), (11135563696009/25000000000000 : ℝ), (22271126808227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1838171601/10000000000 : ℝ)|^17 ≤ (5457745789887/50000000000000 : ℝ)^13
        have hw : |(-1838171601/10000000000 : ℝ)|=(1838171601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693915927/5000000000 : ℝ)|^17 ≤ (11135563696009/25000000000000 : ℝ)^13
        have hw : |(2693915927/5000000000 : ℝ)|=(2693915927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2693915873/5000000000 : ℝ)|^17 ≤ (22271126808227/50000000000000 : ℝ)^13
        have hw : |(2693915873/5000000000 : ℝ)|=(2693915873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_1 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (528575337/1000000000 : ℝ)*x 0 + (-1978254249/10000000000 : ℝ)*x 1 + (673479/1250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528575337/1000000000 : ℝ)^17 ≤ (21720960275581/50000000000000 : ℝ)^13 := by
    have hnat : (528575337 : ℕ)^17*50000000000000^13 ≤ 21720960275581^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528575337 1000000000 21720960275581 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978254249/10000000000 : ℝ)^17 ≤ (3003955767311/25000000000000 : ℝ)^13 := by
    have hnat : (1978254249 : ℕ)^17*25000000000000^13 ≤ 3003955767311^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978254249 10000000000 3003955767311 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673479/1250000 : ℝ)^17 ≤ (22271128181217/50000000000000 : ℝ)^13 := by
    have hnat : (673479 : ℕ)^17*50000000000000^13 ≤ 22271128181217^13*1250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673479 1250000 22271128181217 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528575337/1000000000 : ℝ), (-1978254249/10000000000 : ℝ), (673479/1250000 : ℝ)] ![(21720960275581/50000000000000 : ℝ), (3003955767311/25000000000000 : ℝ), (22271128181217/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528575337/1000000000 : ℝ)|^17 ≤ (21720960275581/50000000000000 : ℝ)^13
        have hw : |(528575337/1000000000 : ℝ)|=(528575337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978254249/10000000000 : ℝ)|^17 ≤ (3003955767311/25000000000000 : ℝ)^13
        have hw : |(-1978254249/10000000000 : ℝ)|=(1978254249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673479/1250000 : ℝ)|^17 ≤ (22271128181217/50000000000000 : ℝ)^13
        have hw : |(673479/1250000 : ℝ)|=(673479/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_2 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5285753009/10000000000 : ℝ)*x 0 + (2693916141/5000000000 : ℝ)*x 1 + (-989127177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285753009/10000000000 : ℝ)^17 ≤ (2715119791957/6250000000000 : ℝ)^13 := by
    have hnat : (5285753009 : ℕ)^17*6250000000000^13 ≤ 2715119791957^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285753009 10000000000 2715119791957 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2693916141/5000000000 : ℝ)^17 ≤ (44542259411121/100000000000000 : ℝ)^13 := by
    have hnat : (2693916141 : ℕ)^17*100000000000000^13 ≤ 44542259411121^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693916141 5000000000 44542259411121 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (989127177/5000000000 : ℝ)^17 ≤ (2403164780649/20000000000000 : ℝ)^13 := by
    have hnat : (989127177 : ℕ)^17*20000000000000^13 ≤ 2403164780649^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989127177 5000000000 2403164780649 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285753009/10000000000 : ℝ), (2693916141/5000000000 : ℝ), (-989127177/5000000000 : ℝ)] ![(2715119791957/6250000000000 : ℝ), (44542259411121/100000000000000 : ℝ), (2403164780649/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285753009/10000000000 : ℝ)|^17 ≤ (2715119791957/6250000000000 : ℝ)^13
        have hw : |(5285753009/10000000000 : ℝ)|=(5285753009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2693916141/5000000000 : ℝ)|^17 ≤ (44542259411121/100000000000000 : ℝ)^13
        have hw : |(2693916141/5000000000 : ℝ)|=(2693916141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-989127177/5000000000 : ℝ)|^17 ≤ (2403164780649/20000000000000 : ℝ)^13
        have hw : |(-989127177/5000000000 : ℝ)|=(989127177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_3 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4460774569/10000000000 : ℝ)*x 0 + (21219837/50000000 : ℝ)*x 1 + (53049601/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460774569/10000000000 : ℝ)^17 ≤ (3479657629829/10000000000000 : ℝ)^13 := by
    have hnat : (4460774569 : ℕ)^17*10000000000000^13 ≤ 3479657629829^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460774569 10000000000 3479657629829 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21219837/50000000 : ℝ)^17 ≤ (32601708425259/100000000000000 : ℝ)^13 := by
    have hnat : (21219837 : ℕ)^17*100000000000000^13 ≤ 32601708425259^13*50000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21219837 50000000 32601708425259 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (53049601/125000000 : ℝ)^17 ≤ (8150428814059/25000000000000 : ℝ)^13 := by
    have hnat : (53049601 : ℕ)^17*25000000000000^13 ≤ 8150428814059^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53049601 125000000 8150428814059 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460774569/10000000000 : ℝ), (21219837/50000000 : ℝ), (53049601/125000000 : ℝ)] ![(3479657629829/10000000000000 : ℝ), (32601708425259/100000000000000 : ℝ), (8150428814059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460774569/10000000000 : ℝ)|^17 ≤ (3479657629829/10000000000000 : ℝ)^13
        have hw : |(4460774569/10000000000 : ℝ)|=(4460774569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21219837/50000000 : ℝ)|^17 ≤ (32601708425259/100000000000000 : ℝ)^13
        have hw : |(21219837/50000000 : ℝ)|=(21219837/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(53049601/125000000 : ℝ)|^17 ≤ (8150428814059/25000000000000 : ℝ)^13
        have hw : |(53049601/125000000 : ℝ)|=(53049601/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_4 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167677883/10000000000 : ℝ)*x 0 + (2632963339/5000000000 : ℝ)*x 1 + (1053185443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167677883/10000000000 : ℝ)^17 ≤ (2708416390681/20000000000000 : ℝ)^13 := by
    have hnat : (2167677883 : ℕ)^17*20000000000000^13 ≤ 2708416390681^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167677883 10000000000 2708416390681 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632963339/5000000000 : ℝ)^17 ≤ (43228956136077/100000000000000 : ℝ)^13 := by
    have hnat : (2632963339 : ℕ)^17*100000000000000^13 ≤ 43228956136077^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632963339 5000000000 43228956136077 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053185443/2000000000 : ℝ)^17 ≤ (21614480950409/50000000000000 : ℝ)^13 := by
    have hnat : (1053185443 : ℕ)^17*50000000000000^13 ≤ 21614480950409^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053185443 2000000000 21614480950409 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167677883/10000000000 : ℝ), (2632963339/5000000000 : ℝ), (1053185443/2000000000 : ℝ)] ![(2708416390681/20000000000000 : ℝ), (43228956136077/100000000000000 : ℝ), (21614480950409/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167677883/10000000000 : ℝ)|^17 ≤ (2708416390681/20000000000000 : ℝ)^13
        have hw : |(-2167677883/10000000000 : ℝ)|=(2167677883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632963339/5000000000 : ℝ)|^17 ≤ (43228956136077/100000000000000 : ℝ)^13
        have hw : |(2632963339/5000000000 : ℝ)|=(2632963339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053185443/2000000000 : ℝ)|^17 ≤ (21614480950409/50000000000000 : ℝ)^13
        have hw : |(1053185443/2000000000 : ℝ)|=(1053185443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_5 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5371197991/10000000000 : ℝ)*x 0 + (-2027508093/10000000000 : ℝ)*x 1 + (5265926853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371197991/10000000000 : ℝ)^17 ≤ (8872502489693/20000000000000 : ℝ)^13 := by
    have hnat : (5371197991 : ℕ)^17*20000000000000^13 ≤ 8872502489693^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371197991 10000000000 8872502489693 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2027508093/10000000000 : ℝ)^17 ≤ (12408529524639/100000000000000 : ℝ)^13 := by
    have hnat : (2027508093 : ℕ)^17*100000000000000^13 ≤ 12408529524639^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027508093 10000000000 12408529524639 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265926853/10000000000 : ℝ)^17 ≤ (43228958014717/100000000000000 : ℝ)^13 := by
    have hnat : (5265926853 : ℕ)^17*100000000000000^13 ≤ 43228958014717^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265926853 10000000000 43228958014717 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371197991/10000000000 : ℝ), (-2027508093/10000000000 : ℝ), (5265926853/10000000000 : ℝ)] ![(8872502489693/20000000000000 : ℝ), (12408529524639/100000000000000 : ℝ), (43228958014717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371197991/10000000000 : ℝ)|^17 ≤ (8872502489693/20000000000000 : ℝ)^13
        have hw : |(5371197991/10000000000 : ℝ)|=(5371197991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2027508093/10000000000 : ℝ)|^17 ≤ (12408529524639/100000000000000 : ℝ)^13
        have hw : |(-2027508093/10000000000 : ℝ)|=(2027508093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265926853/10000000000 : ℝ)|^17 ≤ (43228958014717/100000000000000 : ℝ)^13
        have hw : |(5265926853/10000000000 : ℝ)|=(5265926853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_6 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5371198373/10000000000 : ℝ)*x 0 + (1316481737/2500000000 : ℝ)*x 1 + (-40550149/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5371198373/10000000000 : ℝ)^17 ≤ (44362516574319/100000000000000 : ℝ)^13 := by
    have hnat : (5371198373 : ℕ)^17*100000000000000^13 ≤ 44362516574319^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371198373 10000000000 44362516574319 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316481737/2500000000 : ℝ)^17 ≤ (864579180691/2000000000000 : ℝ)^13 := by
    have hnat : (1316481737 : ℕ)^17*2000000000000^13 ≤ 864579180691^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316481737 2500000000 864579180691 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40550149/200000000 : ℝ)^17 ≤ (6204262189293/50000000000000 : ℝ)^13 := by
    have hnat : (40550149 : ℕ)^17*50000000000000^13 ≤ 6204262189293^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40550149 200000000 6204262189293 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5371198373/10000000000 : ℝ), (1316481737/2500000000 : ℝ), (-40550149/200000000 : ℝ)] ![(44362516574319/100000000000000 : ℝ), (864579180691/2000000000000 : ℝ), (6204262189293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5371198373/10000000000 : ℝ)|^17 ≤ (44362516574319/100000000000000 : ℝ)^13
        have hw : |(5371198373/10000000000 : ℝ)|=(5371198373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316481737/2500000000 : ℝ)|^17 ≤ (864579180691/2000000000000 : ℝ)^13
        have hw : |(1316481737/2500000000 : ℝ)|=(1316481737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40550149/200000000 : ℝ)|^17 ≤ (6204262189293/50000000000000 : ℝ)^13
        have hw : |(-40550149/200000000 : ℝ)|=(40550149/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_7 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (416565851/1000000000 : ℝ)*x 0 + (878294917/2000000000 : ℝ)*x 1 + (4391472987/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416565851/1000000000 : ℝ)^17 ≤ (7954323736321/25000000000000 : ℝ)^13 := by
    have hnat : (416565851 : ℕ)^17*25000000000000^13 ≤ 7954323736321^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416565851 1000000000 7954323736321 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878294917/2000000000 : ℝ)^17 ≤ (34091360629097/100000000000000 : ℝ)^13 := by
    have hnat : (878294917 : ℕ)^17*100000000000000^13 ≤ 34091360629097^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878294917 2000000000 34091360629097 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4391472987/10000000000 : ℝ)^17 ≤ (34091344406653/100000000000000 : ℝ)^13 := by
    have hnat : (4391472987 : ℕ)^17*100000000000000^13 ≤ 34091344406653^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4391472987 10000000000 34091344406653 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(416565851/1000000000 : ℝ), (878294917/2000000000 : ℝ), (4391472987/10000000000 : ℝ)] ![(7954323736321/25000000000000 : ℝ), (34091360629097/100000000000000 : ℝ), (34091344406653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(416565851/1000000000 : ℝ)|^17 ≤ (7954323736321/25000000000000 : ℝ)^13
        have hw : |(416565851/1000000000 : ℝ)|=(416565851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(878294917/2000000000 : ℝ)|^17 ≤ (34091360629097/100000000000000 : ℝ)^13
        have hw : |(878294917/2000000000 : ℝ)|=(878294917/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4391472987/10000000000 : ℝ)|^17 ≤ (34091344406653/100000000000000 : ℝ)^13
        have hw : |(4391472987/10000000000 : ℝ)|=(4391472987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_8 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098358641/10000000000 : ℝ)*x 0 + (1036354783/2000000000 : ℝ)*x 1 + (5401827127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098358641/10000000000 : ℝ)^17 ≤ (12978584322163/100000000000000 : ℝ)^13 := by
    have hnat : (2098358641 : ℕ)^17*100000000000000^13 ≤ 12978584322163^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098358641 10000000000 12978584322163 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036354783/2000000000 : ℝ)^17 ≤ (42327798300689/100000000000000 : ℝ)^13 := by
    have hnat : (1036354783 : ℕ)^17*100000000000000^13 ≤ 42327798300689^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036354783 2000000000 42327798300689 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401827127/10000000000 : ℝ)^17 ≤ (11173404341263/25000000000000 : ℝ)^13 := by
    have hnat : (5401827127 : ℕ)^17*25000000000000^13 ≤ 11173404341263^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401827127 10000000000 11173404341263 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098358641/10000000000 : ℝ), (1036354783/2000000000 : ℝ), (5401827127/10000000000 : ℝ)] ![(12978584322163/100000000000000 : ℝ), (42327798300689/100000000000000 : ℝ), (11173404341263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098358641/10000000000 : ℝ)|^17 ≤ (12978584322163/100000000000000 : ℝ)^13
        have hw : |(-2098358641/10000000000 : ℝ)|=(2098358641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036354783/2000000000 : ℝ)|^17 ≤ (42327798300689/100000000000000 : ℝ)^13
        have hw : |(1036354783/2000000000 : ℝ)|=(1036354783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401827127/10000000000 : ℝ)|^17 ≤ (11173404341263/25000000000000 : ℝ)^13
        have hw : |(5401827127/10000000000 : ℝ)|=(5401827127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_9 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5275939497/10000000000 : ℝ)*x 0 + (-1972471247/10000000000 : ℝ)*x 1 + (1350456699/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275939497/10000000000 : ℝ)^17 ≤ (43336476034333/100000000000000 : ℝ)^13 := by
    have hnat : (5275939497 : ℕ)^17*100000000000000^13 ≤ 43336476034333^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275939497 10000000000 43336476034333 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972471247/10000000000 : ℝ)^17 ≤ (5984955078793/50000000000000 : ℝ)^13 := by
    have hnat : (1972471247 : ℕ)^17*50000000000000^13 ≤ 5984955078793^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972471247 10000000000 5984955078793 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350456699/2500000000 : ℝ)^17 ≤ (11173403445943/25000000000000 : ℝ)^13 := by
    have hnat : (1350456699 : ℕ)^17*25000000000000^13 ≤ 11173403445943^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350456699 2500000000 11173403445943 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275939497/10000000000 : ℝ), (-1972471247/10000000000 : ℝ), (1350456699/2500000000 : ℝ)] ![(43336476034333/100000000000000 : ℝ), (5984955078793/50000000000000 : ℝ), (11173403445943/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275939497/10000000000 : ℝ)|^17 ≤ (43336476034333/100000000000000 : ℝ)^13
        have hw : |(5275939497/10000000000 : ℝ)|=(5275939497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1972471247/10000000000 : ℝ)|^17 ≤ (5984955078793/50000000000000 : ℝ)^13
        have hw : |(-1972471247/10000000000 : ℝ)|=(1972471247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350456699/2500000000 : ℝ)|^17 ≤ (11173403445943/25000000000000 : ℝ)^13
        have hw : |(1350456699/2500000000 : ℝ)|=(1350456699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_10 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5275938781/10000000000 : ℝ)*x 0 + (2700913301/5000000000 : ℝ)*x 1 + (-986236241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275938781/10000000000 : ℝ)^17 ≤ (21668234171759/50000000000000 : ℝ)^13 := by
    have hnat : (5275938781 : ℕ)^17*50000000000000^13 ≤ 21668234171759^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275938781 10000000000 21668234171759 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700913301/5000000000 : ℝ)^17 ≤ (44693611684773/100000000000000 : ℝ)^13 := by
    have hnat : (2700913301 : ℕ)^17*100000000000000^13 ≤ 44693611684773^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700913301 5000000000 44693611684773 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986236241/5000000000 : ℝ)^17 ≤ (2992479989547/25000000000000 : ℝ)^13 := by
    have hnat : (986236241 : ℕ)^17*25000000000000^13 ≤ 2992479989547^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986236241 5000000000 2992479989547 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275938781/10000000000 : ℝ), (2700913301/5000000000 : ℝ), (-986236241/5000000000 : ℝ)] ![(21668234171759/50000000000000 : ℝ), (44693611684773/100000000000000 : ℝ), (2992479989547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275938781/10000000000 : ℝ)|^17 ≤ (21668234171759/50000000000000 : ℝ)^13
        have hw : |(5275938781/10000000000 : ℝ)|=(5275938781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700913301/5000000000 : ℝ)|^17 ≤ (44693611684773/100000000000000 : ℝ)^13
        have hw : |(2700913301/5000000000 : ℝ)|=(2700913301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-986236241/5000000000 : ℝ)|^17 ≤ (2992479989547/25000000000000 : ℝ)^13
        have hw : |(-986236241/5000000000 : ℝ)|=(986236241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_11 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4494096023/10000000000 : ℝ)*x 0 + (52837741/125000000 : ℝ)*x 1 + (4227020317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4494096023/10000000000 : ℝ)^17 ≤ (3513686983861/10000000000000 : ℝ)^13 := by
    have hnat : (4494096023 : ℕ)^17*10000000000000^13 ≤ 3513686983861^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494096023 10000000000 3513686983861 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52837741/125000000 : ℝ)^17 ≤ (8107889967147/25000000000000 : ℝ)^13 := by
    have hnat : (52837741 : ℕ)^17*25000000000000^13 ≤ 8107889967147^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52837741 125000000 8107889967147 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4227020317/10000000000 : ℝ)^17 ≤ (3243157027301/10000000000000 : ℝ)^13 := by
    have hnat : (4227020317 : ℕ)^17*10000000000000^13 ≤ 3243157027301^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227020317 10000000000 3243157027301 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4494096023/10000000000 : ℝ), (52837741/125000000 : ℝ), (4227020317/10000000000 : ℝ)] ![(3513686983861/10000000000000 : ℝ), (8107889967147/25000000000000 : ℝ), (3243157027301/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4494096023/10000000000 : ℝ)|^17 ≤ (3513686983861/10000000000000 : ℝ)^13
        have hw : |(4494096023/10000000000 : ℝ)|=(4494096023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52837741/125000000 : ℝ)|^17 ≤ (8107889967147/25000000000000 : ℝ)^13
        have hw : |(52837741/125000000 : ℝ)|=(52837741/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4227020317/10000000000 : ℝ)|^17 ≤ (3243157027301/10000000000000 : ℝ)^13
        have hw : |(4227020317/10000000000 : ℝ)|=(4227020317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_12 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-476933759/2500000000 : ℝ)*x 0 + (1367471713/2500000000 : ℝ)*x 1 + (1050964407/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (476933759/2500000000 : ℝ)^17 ≤ (5729398107179/50000000000000 : ℝ)^13 := by
    have hnat : (476933759 : ℕ)^17*50000000000000^13 ≤ 5729398107179^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      476933759 2500000000 5729398107179 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367471713/2500000000 : ℝ)^17 ≤ (11357854558199/25000000000000 : ℝ)^13 := by
    have hnat : (1367471713 : ℕ)^17*25000000000000^13 ≤ 11357854558199^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367471713 2500000000 11357854558199 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050964407/2000000000 : ℝ)^17 ≤ (1347180798029/3125000000000 : ℝ)^13 := by
    have hnat : (1050964407 : ℕ)^17*3125000000000^13 ≤ 1347180798029^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050964407 2000000000 1347180798029 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-476933759/2500000000 : ℝ), (1367471713/2500000000 : ℝ), (1050964407/2000000000 : ℝ)] ![(5729398107179/50000000000000 : ℝ), (11357854558199/25000000000000 : ℝ), (1347180798029/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-476933759/2500000000 : ℝ)|^17 ≤ (5729398107179/50000000000000 : ℝ)^13
        have hw : |(-476933759/2500000000 : ℝ)|=(476933759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367471713/2500000000 : ℝ)|^17 ≤ (11357854558199/25000000000000 : ℝ)^13
        have hw : |(1367471713/2500000000 : ℝ)|=(1367471713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050964407/2000000000 : ℝ)|^17 ≤ (1347180798029/3125000000000 : ℝ)^13
        have hw : |(1050964407/2000000000 : ℝ)|=(1050964407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_13 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2689490021/5000000000 : ℝ)*x 0 + (-1015946517/5000000000 : ℝ)*x 1 + (210192871/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689490021/5000000000 : ℝ)^17 ≤ (44446582511969/100000000000000 : ℝ)^13 := by
    have hnat : (2689490021 : ℕ)^17*100000000000000^13 ≤ 44446582511969^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689490021 5000000000 44446582511969 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015946517/5000000000 : ℝ)^17 ≤ (155545434057/1250000000000 : ℝ)^13 := by
    have hnat : (1015946517 : ℕ)^17*1250000000000^13 ≤ 155545434057^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015946517 5000000000 155545434057 1250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210192871/400000000 : ℝ)^17 ≤ (21554891373809/50000000000000 : ℝ)^13 := by
    have hnat : (210192871 : ℕ)^17*50000000000000^13 ≤ 21554891373809^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210192871 400000000 21554891373809 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689490021/5000000000 : ℝ), (-1015946517/5000000000 : ℝ), (210192871/400000000 : ℝ)] ![(44446582511969/100000000000000 : ℝ), (155545434057/1250000000000 : ℝ), (21554891373809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689490021/5000000000 : ℝ)|^17 ≤ (44446582511969/100000000000000 : ℝ)^13
        have hw : |(2689490021/5000000000 : ℝ)|=(2689490021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1015946517/5000000000 : ℝ)|^17 ≤ (155545434057/1250000000000 : ℝ)^13
        have hw : |(-1015946517/5000000000 : ℝ)|=(1015946517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210192871/400000000 : ℝ)|^17 ≤ (21554891373809/50000000000000 : ℝ)^13
        have hw : |(210192871/400000000 : ℝ)|=(210192871/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_14 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (268949003/500000000 : ℝ)*x 0 + (5254821781/10000000000 : ℝ)*x 1 + (-1015946501/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268949003/500000000 : ℝ)^17 ≤ (11111645676617/25000000000000 : ℝ)^13 := by
    have hnat : (268949003 : ℕ)^17*25000000000000^13 ≤ 11111645676617^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268949003 500000000 11111645676617 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254821781/10000000000 : ℝ)^17 ≤ (43109782811987/100000000000000 : ℝ)^13 := by
    have hnat : (5254821781 : ℕ)^17*100000000000000^13 ≤ 43109782811987^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254821781 10000000000 43109782811987 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015946501/5000000000 : ℝ)^17 ≤ (194431788567/1562500000000 : ℝ)^13 := by
    have hnat : (1015946501 : ℕ)^17*1562500000000^13 ≤ 194431788567^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015946501 5000000000 194431788567 1562500000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268949003/500000000 : ℝ), (5254821781/10000000000 : ℝ), (-1015946501/5000000000 : ℝ)] ![(11111645676617/25000000000000 : ℝ), (43109782811987/100000000000000 : ℝ), (194431788567/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268949003/500000000 : ℝ)|^17 ≤ (11111645676617/25000000000000 : ℝ)^13
        have hw : |(268949003/500000000 : ℝ)|=(268949003/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254821781/10000000000 : ℝ)|^17 ≤ (43109782811987/100000000000000 : ℝ)^13
        have hw : |(5254821781/10000000000 : ℝ)|=(5254821781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1015946501/5000000000 : ℝ)|^17 ≤ (194431788567/1562500000000 : ℝ)^13
        have hw : |(-1015946501/5000000000 : ℝ)|=(1015946501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1392_box_15 (p : ℝ) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (827665177/2000000000 : ℝ)*x 0 + (110122501/250000000 : ℝ)*x 1 + (1101224991/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827665177/2000000000 : ℝ)^17 ≤ (15772284261491/50000000000000 : ℝ)^13 := by
    have hnat : (827665177 : ℕ)^17*50000000000000^13 ≤ 15772284261491^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827665177 2000000000 15772284261491 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110122501/250000000 : ℝ)^17 ≤ (4278464514343/12500000000000 : ℝ)^13 := by
    have hnat : (110122501 : ℕ)^17*12500000000000^13 ≤ 4278464514343^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110122501 250000000 4278464514343 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101224991/2500000000 : ℝ)^17 ≤ (4278464417811/12500000000000 : ℝ)^13 := by
    have hnat : (1101224991 : ℕ)^17*12500000000000^13 ≤ 4278464417811^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101224991 2500000000 4278464417811 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827665177/2000000000 : ℝ), (110122501/250000000 : ℝ), (1101224991/2500000000 : ℝ)] ![(15772284261491/50000000000000 : ℝ), (4278464514343/12500000000000 : ℝ), (4278464417811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827665177/2000000000 : ℝ)|^17 ≤ (15772284261491/50000000000000 : ℝ)^13
        have hw : |(827665177/2000000000 : ℝ)|=(827665177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110122501/250000000 : ℝ)|^17 ≤ (4278464514343/12500000000000 : ℝ)^13
        have hw : |(110122501/250000000 : ℝ)|=(110122501/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101224991/2500000000 : ℝ)|^17 ≤ (4278464417811/12500000000000 : ℝ)^13
        have hw : |(1101224991/2500000000 : ℝ)|=(1101224991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1392_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31439/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59039/100000 : ℝ) ∧ (40121/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (16909/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (921/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (921/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (921/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11263/100000 : ℝ) ^ (4351/1024 : ℝ) ≤ (9342346621796391/100000000000000000000 : ℝ) := by
    have hpowers : (11263/100000 : ℝ)^4351 ≤ (9342346621796391/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11263 : ℕ)^4351*100000000000000000000^1024 ≤ 9342346621796391^1024*100000^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11263 100000 9342346621796391 100000000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11263/100000 : ℝ)) (X := (9342346621796391/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (921/6250 : ℝ) ^ (4351/1024 : ℝ) ≤ (1829386632174181/6250000000000000000 : ℝ) := by
    have hpowers : (921/6250 : ℝ)^4351 ≤ (1829386632174181/6250000000000000000 : ℝ)^1024 := by
      have hnat : (921 : ℕ)^4351*6250000000000000000^1024 ≤ 1829386632174181^1024*6250^4351 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        921 6250 1829386632174181 6250000000000000000 4351 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (921/6250 : ℝ)) (X := (1829386632174181/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009342346621796391/50000000000000000000 : ℝ) ≤ (2000087941894873/2000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (50009342346621796391/50000000000000000000 : ℝ)^1024 ≤ (2000087941894873/2000000000000000 : ℝ)^4351 := by
      have hnat : (50009342346621796391 : ℕ)^1024*2000000000000000^4351 ≤ 2000087941894873^4351*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009342346621796391 50000000000000000000 2000087941894873 2000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000087941894873/2000000000000000 : ℝ)) (X := (50009342346621796391/50000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038612532736583287/100000000000000000000 : ℝ) ≤ (312528393902149/312500000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (100038612532736583287/100000000000000000000 : ℝ)^1024 ≤ (312528393902149/312500000000000 : ℝ)^4351 := by
      have hnat : (100038612532736583287 : ℕ)^1024*312500000000000^4351 ≤ 312528393902149^4351*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038612532736583287 100000000000000000000 312528393902149 312500000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312528393902149/312500000000000 : ℝ)) (X := (100038612532736583287/100000000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126829386632174181/3125000000000000000 : ℝ) ≤ (10001377500263171/10000000000000000 : ℝ) ^ (4351/1024 : ℝ) := by
    have hpowers : (3126829386632174181/3125000000000000000 : ℝ)^1024 ≤ (10001377500263171/10000000000000000 : ℝ)^4351 := by
      have hnat : (3126829386632174181 : ℕ)^1024*10000000000000000^4351 ≤ 10001377500263171^4351*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126829386632174181 3125000000000000000 10001377500263171 10000000000000000 1024 4351 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001377500263171/10000000000000000 : ℝ)) (X := (3126829386632174181/3125000000000000000 : ℝ)) (by norm_num) 4351 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9342346621796391/100000000000000000000 : ℝ) ≤ ((34720964773350147667/34730000000000000000 : ℝ)+2*(468895394403/347300000000000 : ℝ)*(11263/100000 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (34720964773350147667/34730000000000000000 : ℝ)+2*(468895394403/347300000000000 : ℝ)*(11263/100000 : ℝ)=(2000087941894873/2000000000000000 : ℝ) by norm_num, show 1+2*(9342346621796391/100000000000000000000 : ℝ)=(50009342346621796391/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1829386632174181/6250000000000000000 : ℝ)+(9342346621796391/100000000000000000000 : ℝ) ≤ ((34720964773350147667/34730000000000000000 : ℝ)+(468895394403/347300000000000 : ℝ)*((921/6250 : ℝ)+(11263/100000 : ℝ)))^(4351/1024 : ℝ) := by
    rw [show (34720964773350147667/34730000000000000000 : ℝ)+(468895394403/347300000000000 : ℝ)*((921/6250 : ℝ)+(11263/100000 : ℝ))=(312528393902149/312500000000000 : ℝ) by norm_num, show 1+(1829386632174181/6250000000000000000 : ℝ)+(9342346621796391/100000000000000000000 : ℝ)=(100038612532736583287/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1829386632174181/6250000000000000000 : ℝ) ≤ ((34720964773350147667/34730000000000000000 : ℝ)+2*(468895394403/347300000000000 : ℝ)*(921/6250 : ℝ))^(4351/1024 : ℝ) := by
    rw [show (34720964773350147667/34730000000000000000 : ℝ)+2*(468895394403/347300000000000 : ℝ)*(921/6250 : ℝ)=(10001377500263171/10000000000000000 : ℝ) by norm_num, show 1+2*(1829386632174181/6250000000000000000 : ℝ)=(3126829386632174181/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34720964773350147667/34730000000000000000 : ℝ)*(X 1 0+X 2 0)+(468895394403/347300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (34720964773350147667/34730000000000000000 : ℝ)) (alpha := (468895394403/347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34720964773350147667/34730000000000000000 : ℝ)*(X 0 1+X 2 1)+(468895394403/347300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (34720964773350147667/34730000000000000000 : ℝ)) (alpha := (468895394403/347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34720964773350147667/34730000000000000000 : ℝ)*(X 0 2+X 1 2)+(468895394403/347300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4351/1024 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (921/6250 : ℝ)) (c := (34720964773350147667/34730000000000000000 : ℝ)) (alpha := (468895394403/347300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1838171601/10000000000 : ℝ)*X 0 0+(2693915927/5000000000 : ℝ)*X 0 1+(2693915873/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((528575337/1000000000 : ℝ)*X 1 0+(-1978254249/10000000000 : ℝ)*X 1 1+(673479/1250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285753009/10000000000 : ℝ)*X 2 0+(2693916141/5000000000 : ℝ)*X 2 1+(-989127177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4460774569/10000000000 : ℝ)*X 0 0+(21219837/50000000 : ℝ)*X 0 1+(53049601/125000000 : ℝ)*X 0 2+(4460774569/10000000000 : ℝ)*X 1 0+(21219837/50000000 : ℝ)*X 1 1+(53049601/125000000 : ℝ)*X 1 2+(4460774569/10000000000 : ℝ)*X 2 0+(21219837/50000000 : ℝ)*X 2 1+(53049601/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2167677883/10000000000 : ℝ)*X 0 0+(2632963339/5000000000 : ℝ)*X 0 1+(1053185443/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5371197991/10000000000 : ℝ)*X 1 0+(-2027508093/10000000000 : ℝ)*X 1 1+(5265926853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5371198373/10000000000 : ℝ)*X 2 0+(1316481737/2500000000 : ℝ)*X 2 1+(-40550149/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((416565851/1000000000 : ℝ)*X 0 0+(878294917/2000000000 : ℝ)*X 0 1+(4391472987/10000000000 : ℝ)*X 0 2+(416565851/1000000000 : ℝ)*X 1 0+(878294917/2000000000 : ℝ)*X 1 1+(4391472987/10000000000 : ℝ)*X 1 2+(416565851/1000000000 : ℝ)*X 2 0+(878294917/2000000000 : ℝ)*X 2 1+(4391472987/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2098358641/10000000000 : ℝ)*X 0 0+(1036354783/2000000000 : ℝ)*X 0 1+(5401827127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275939497/10000000000 : ℝ)*X 1 0+(-1972471247/10000000000 : ℝ)*X 1 1+(1350456699/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275938781/10000000000 : ℝ)*X 2 0+(2700913301/5000000000 : ℝ)*X 2 1+(-986236241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4494096023/10000000000 : ℝ)*X 0 0+(52837741/125000000 : ℝ)*X 0 1+(4227020317/10000000000 : ℝ)*X 0 2+(4494096023/10000000000 : ℝ)*X 1 0+(52837741/125000000 : ℝ)*X 1 1+(4227020317/10000000000 : ℝ)*X 1 2+(4494096023/10000000000 : ℝ)*X 2 0+(52837741/125000000 : ℝ)*X 2 1+(4227020317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-476933759/2500000000 : ℝ)*X 0 0+(1367471713/2500000000 : ℝ)*X 0 1+(1050964407/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2689490021/5000000000 : ℝ)*X 1 0+(-1015946517/5000000000 : ℝ)*X 1 1+(210192871/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((268949003/500000000 : ℝ)*X 2 0+(5254821781/10000000000 : ℝ)*X 2 1+(-1015946501/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((827665177/2000000000 : ℝ)*X 0 0+(110122501/250000000 : ℝ)*X 0 1+(1101224991/2500000000 : ℝ)*X 0 2+(827665177/2000000000 : ℝ)*X 1 0+(110122501/250000000 : ℝ)*X 1 1+(1101224991/2500000000 : ℝ)*X 1 2+(827665177/2000000000 : ℝ)*X 2 0+(110122501/250000000 : ℝ)*X 2 1+(1101224991/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1392_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31439/50000 : ℝ) ≤ (-272959275057952031498268309456177/434125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (138109123/100000000000000 : ℝ)*(upper1) + (34338253/12500000000000 : ℝ)*(lower2) + (50913869/100000000000000 : ℝ)*(upper4) + (744087160115059/25000000000000 : ℝ)*(major0) + (744087160115059/25000000000000 : ℝ)*(major1) + (744087160115059/25000000000000 : ℝ)*(major2) + (438087281/6250000000000 : ℝ)*(sp1) + (4552334481/100000000000000 : ℝ)*(sp3) + (4074283200579157/100000000000000 : ℝ)*(sp4) + (509285223567343/12500000000000 : ℝ)*(sp5) + (2037073662032397/50000000000000 : ℝ)*(sp6) + (949681254126903/50000000000000 : ℝ)*(sp7) + (5597356083/100000000000000 : ℝ)*(sp8) + (70736935223/50000000000000 : ℝ)*(sp14) + (949683530294143/50000000000000 : ℝ)*(f.failure) + (101857219948381/2500000000000 : ℝ)*(f.sum) + (2770604360133/17365000000000000000000000000 : ℝ)*base65 + (6366662864244867353/868250000000000000000000000000000 : ℝ)*base67 + (7503062328599617353/868250000000000000000000000000000 : ℝ)*base69 + (6061392874080867353/868250000000000000000000000000000 : ℝ)*base71 + (34238285951001/8682500000000000000000000000 : ℝ)*base74 + (10749237802117617353/868250000000000000000000000000000 : ℝ)*base75 + (9239160004992367353/868250000000000000000000000000000 : ℝ)*base77 + (8205071409737117353/868250000000000000000000000000000 : ℝ)*base79 + (12010196828271/8682500000000000000000000000 : ℝ)*base82 + (6537541/500000000000000000000 : ℝ)*base90 + (6537541/500000000000000000000 : ℝ)*base92 + (6537541/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (59039/100000 : ℝ) ≤ (128157784459237532043739046723709/217062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18191877/25000000000000 : ℝ)*(lower1) + (51164623/50000000000000 : ℝ)*(upper2) + (18842711/100000000000000 : ℝ)*(lower4) + (380839535250791/12500000000000 : ℝ)*(major0) + (380839535250791/12500000000000 : ℝ)*(major1) + (380839535250791/12500000000000 : ℝ)*(major2) + (4129474651613237/100000000000000 : ℝ)*(sp0) + (516183946591601/12500000000000 : ℝ)*(sp1) + (1032367076823447/25000000000000 : ℝ)*(sp2) + (1944268996508633/100000000000000 : ℝ)*(sp3) + (318097213/4000000000000 : ℝ)*(sp5) + (2243573869/20000000000000 : ℝ)*(sp6) + (683021689/20000000000000 : ℝ)*(sp7) + (4873549897/100000000000000 : ℝ)*(sp12) + (972136205808539/50000000000000 : ℝ)*(f.failure) + (2064739762581567/50000000000000 : ℝ)*(f.sum) + (16439628732957/8682500000000000000000000000 : ℝ)*base65 + (137575381506979597/434125000000000000000000000000000 : ℝ)*base67 + (1370823138068645403/434125000000000000000000000000000 : ℝ)*base70 + (1712522539197395403/434125000000000000000000000000000 : ℝ)*base72 + (7021514334559/4341250000000000000000000000 : ℝ)*base74 + (3156548826900854597/434125000000000000000000000000000 : ℝ)*base75 + (130102033806854597/434125000000000000000000000000000 : ℝ)*base77 + (2282080107396729597/434125000000000000000000000000000 : ℝ)*base79 + (23590037302839/17365000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3348807/500000000000000000000 : ℝ)*base89 + (3348807/500000000000000000000 : ℝ)*base91 + (3348807/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (40121/50000 : ℝ) ≤ (1393446261886530227517506674129083/1736500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (210572099/100000000000000 : ℝ)*(upper0) + (329688379/100000000000000 : ℝ)*(upper1) + (349344307/50000000000000 : ℝ)*(upper2) + (3356562666939917/100000000000000 : ℝ)*(major0) + (3356562666939917/100000000000000 : ℝ)*(major1) + (3356562666939917/100000000000000 : ℝ)*(major2) + (46407812689/10000000000000 : ℝ)*(sp1) + (2092090959/2500000000000 : ℝ)*(sp2) + (44911082511/50000000000000 : ℝ)*(sp3) + (34598867943/100000000000000 : ℝ)*(sp4) + (2272170308447803/50000000000000 : ℝ)*(sp8) + (2271955568818329/50000000000000 : ℝ)*(sp9) + (4544291532125189/100000000000000 : ℝ)*(sp10) + (2141912119314597/100000000000000 : ℝ)*(sp11) + (107100097073981/5000000000000 : ℝ)*(f.failure) + (4544375215763549/100000000000000 : ℝ)*(f.sum) + (64481485252641/17365000000000000000000000000 : ℝ)*base65 + (10989131418129823639/3473000000000000000000000000000000 : ℝ)*base67 + (15242173328246176361/3473000000000000000000000000000000 : ℝ)*base70 + (34500786533446823639/3473000000000000000000000000000000 : ℝ)*base71 + (152135704115791/17365000000000000000000000000 : ℝ)*base73 + (43638738524900823639/3473000000000000000000000000000000 : ℝ)*base75 + (40934590150067823639/3473000000000000000000000000000000 : ℝ)*base77 + (43413379980612176361/3473000000000000000000000000000000 : ℝ)*base80 + (21405585591409/4341250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (527953/50000000000000000000 : ℝ)*base89 + (527953/50000000000000000000 : ℝ)*base91 + (527953/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-16909/20000 : ℝ) ≤ (-734038383757877298294391882768707/868250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9877173/12500000000000 : ℝ)*(lower0) + (24552301/100000000000000 : ℝ)*(lower1) + (1888717/20000000000000 : ℝ)*(lower2) + (32235481/50000000000000 : ℝ)*(lower3) + (10810383/50000000000000 : ℝ)*(lower4) + (1696805011777431/50000000000000 : ℝ)*(major0) + (1696805011777431/50000000000000 : ℝ)*(major1) + (1696805011777431/50000000000000 : ℝ)*(major2) + (72917110207/100000000000000 : ℝ)*(sp5) + (99324492137/100000000000000 : ℝ)*(sp6) + (4649756969792789/100000000000000 : ℝ)*(sp12) + (2324842026341291/50000000000000 : ℝ)*(sp13) + (4649657645300651/100000000000000 : ℝ)*(sp14) + (1082821919381333/50000000000000 : ℝ)*(sp15) + (1082821919381333/50000000000000 : ℝ)*(f.failure) + (4649756969792789/100000000000000 : ℝ)*(f.sum) + (32413165769201/4341250000000000000000000000 : ℝ)*base66 + (11810899191424796523/1736500000000000000000000000000000 : ℝ)*base68 + (15317817848266296523/1736500000000000000000000000000000 : ℝ)*base70 + (27061563052514296523/1736500000000000000000000000000000 : ℝ)*base72 + (27924056846021/17365000000000000000000000000 : ℝ)*base73 + (5310726077685296523/1736500000000000000000000000000000 : ℝ)*base76 + (11844074508184296523/1736500000000000000000000000000000 : ℝ)*base78 + (5030174189108296523/1736500000000000000000000000000000 : ℝ)*base80 + (6107669923947/8682500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6333929/500000000000000000000 : ℝ)*base89 + (6333929/500000000000000000000 : ℝ)*base91 + (6333929/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1392_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (921/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31439/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59039/100000 : ℝ) else (40121/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16909/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1392_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1392_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31439/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59039/100000 : ℝ) else (40121/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16909/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1392_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1392_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1392_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4351/1024 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15670213/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7371/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11257/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31439/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(59039/100000 : ℝ) else (40121/50000 : ℝ) ≤ X j i ∧ X j i ≤ (16909/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1392_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
