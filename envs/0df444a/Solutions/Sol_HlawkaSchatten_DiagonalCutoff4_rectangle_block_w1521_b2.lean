-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1521_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:57:46.881345+00:00
-- url     : https://prove2.me/submissions/04867e21-8eee-45a1-a010-cc7bff52b598

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
theorem support_rectangle_w1521_s6_0 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070217211/2000000000 : ℝ)*x 0 + (-1964375749/10000000000 : ℝ)*x 1 + (2609039409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070217211/2000000000 : ℝ)^4539 ≤ (44599588512817/100000000000000 : ℝ)^3515 := by
    have hnat : (1070217211 : ℕ)^4539*100000000000000^3515 ≤ 44599588512817^3515*2000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070217211 2000000000 44599588512817 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1964375749/10000000000 : ℝ)^4539 ≤ (3056783649241/25000000000000 : ℝ)^3515 := by
    have hnat : (1964375749 : ℕ)^4539*25000000000000^3515 ≤ 3056783649241^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964375749 10000000000 3056783649241 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609039409/5000000000 : ℝ)^4539 ≤ (43173276877063/100000000000000 : ℝ)^3515 := by
    have hnat : (2609039409 : ℕ)^4539*100000000000000^3515 ≤ 43173276877063^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609039409 5000000000 43173276877063 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070217211/2000000000 : ℝ), (-1964375749/10000000000 : ℝ), (2609039409/5000000000 : ℝ)] ![(44599588512817/100000000000000 : ℝ), (3056783649241/25000000000000 : ℝ), (43173276877063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070217211/2000000000 : ℝ)|^4539 ≤ (44599588512817/100000000000000 : ℝ)^3515
        have hw : |(1070217211/2000000000 : ℝ)|=(1070217211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1964375749/10000000000 : ℝ)|^4539 ≤ (3056783649241/25000000000000 : ℝ)^3515
        have hw : |(-1964375749/10000000000 : ℝ)|=(1964375749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609039409/5000000000 : ℝ)|^4539 ≤ (43173276877063/100000000000000 : ℝ)^3515
        have hw : |(2609039409/5000000000 : ℝ)|=(2609039409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s6_1 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1854830697/10000000000 : ℝ)*x 0 + (5219182809/10000000000 : ℝ)*x 1 + (678869139/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1854830697/10000000000 : ℝ)^4539 ≤ (11353886613703/100000000000000 : ℝ)^3515 := by
    have hnat : (1854830697 : ℕ)^4539*100000000000000^3515 ≤ 11353886613703^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854830697 10000000000 11353886613703 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219182809/10000000000 : ℝ)^4539 ≤ (10796268106439/25000000000000 : ℝ)^3515 := by
    have hnat : (5219182809 : ℕ)^4539*25000000000000^3515 ≤ 10796268106439^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219182809 10000000000 10796268106439 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678869139/1250000000 : ℝ)^4539 ≤ (45461040953201/100000000000000 : ℝ)^3515 := by
    have hnat : (678869139 : ℕ)^4539*100000000000000^3515 ≤ 45461040953201^3515*1250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678869139 1250000000 45461040953201 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1854830697/10000000000 : ℝ), (5219182809/10000000000 : ℝ), (678869139/1250000000 : ℝ)] ![(11353886613703/100000000000000 : ℝ), (10796268106439/25000000000000 : ℝ), (45461040953201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1854830697/10000000000 : ℝ)|^4539 ≤ (11353886613703/100000000000000 : ℝ)^3515
        have hw : |(-1854830697/10000000000 : ℝ)|=(1854830697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219182809/10000000000 : ℝ)|^4539 ≤ (10796268106439/25000000000000 : ℝ)^3515
        have hw : |(5219182809/10000000000 : ℝ)|=(5219182809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678869139/1250000000 : ℝ)|^4539 ≤ (45461040953201/100000000000000 : ℝ)^3515
        have hw : |(678869139/1250000000 : ℝ)|=(678869139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s6_2 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647418521/5000000000 : ℝ)*x 0 + (-1751501517/10000000000 : ℝ)*x 1 + (1357738261/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647418521/5000000000 : ℝ)^4539 ≤ (21997561494449/50000000000000 : ℝ)^3515 := by
    have hnat : (2647418521 : ℕ)^4539*50000000000000^3515 ≤ 21997561494449^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647418521 5000000000 21997561494449 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1751501517/10000000000 : ℝ)^4539 ≤ (10543836779383/100000000000000 : ℝ)^3515 := by
    have hnat : (1751501517 : ℕ)^4539*100000000000000^3515 ≤ 10543836779383^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751501517 10000000000 10543836779383 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357738261/2500000000 : ℝ)^4539 ≤ (5682630027271/12500000000000 : ℝ)^3515 := by
    have hnat : (1357738261 : ℕ)^4539*12500000000000^3515 ≤ 5682630027271^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357738261 2500000000 5682630027271 12500000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647418521/5000000000 : ℝ), (-1751501517/10000000000 : ℝ), (1357738261/2500000000 : ℝ)] ![(21997561494449/50000000000000 : ℝ), (10543836779383/100000000000000 : ℝ), (5682630027271/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647418521/5000000000 : ℝ)|^4539 ≤ (21997561494449/50000000000000 : ℝ)^3515
        have hw : |(2647418521/5000000000 : ℝ)|=(2647418521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1751501517/10000000000 : ℝ)|^4539 ≤ (10543836779383/100000000000000 : ℝ)^3515
        have hw : |(-1751501517/10000000000 : ℝ)|=(1751501517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357738261/2500000000 : ℝ)|^4539 ≤ (5682630027271/12500000000000 : ℝ)^3515
        have hw : |(1357738261/2500000000 : ℝ)|=(1357738261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s6_3 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647418467/5000000000 : ℝ)*x 0 + (1357738269/2500000000 : ℝ)*x 1 + (-1751501621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647418467/5000000000 : ℝ)^4539 ≤ (10998780457523/25000000000000 : ℝ)^3515 := by
    have hnat : (2647418467 : ℕ)^4539*25000000000000^3515 ≤ 10998780457523^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647418467 5000000000 10998780457523 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357738269/2500000000 : ℝ)^4539 ≤ (22730520282033/50000000000000 : ℝ)^3515 := by
    have hnat : (1357738269 : ℕ)^4539*50000000000000^3515 ≤ 22730520282033^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357738269 2500000000 22730520282033 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1751501621/10000000000 : ℝ)^4539 ≤ (10543837587839/100000000000000 : ℝ)^3515 := by
    have hnat : (1751501621 : ℕ)^4539*100000000000000^3515 ≤ 10543837587839^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1751501621 10000000000 10543837587839 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647418467/5000000000 : ℝ), (1357738269/2500000000 : ℝ), (-1751501621/10000000000 : ℝ)] ![(10998780457523/25000000000000 : ℝ), (22730520282033/50000000000000 : ℝ), (10543837587839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647418467/5000000000 : ℝ)|^4539 ≤ (10998780457523/25000000000000 : ℝ)^3515
        have hw : |(2647418467/5000000000 : ℝ)|=(2647418467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357738269/2500000000 : ℝ)|^4539 ≤ (22730520282033/50000000000000 : ℝ)^3515
        have hw : |(1357738269/2500000000 : ℝ)|=(1357738269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1751501621/10000000000 : ℝ)|^4539 ≤ (10543837587839/100000000000000 : ℝ)^3515
        have hw : |(-1751501621/10000000000 : ℝ)|=(1751501621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_s6_4 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1066416097/2500000000 : ℝ)*x 0 + (902624769/2000000000 : ℝ)*x 1 + (2014935223/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1066416097/2500000000 : ℝ)^4539 ≤ (33280767263381/100000000000000 : ℝ)^3515 := by
    have hnat : (1066416097 : ℕ)^4539*100000000000000^3515 ≤ 33280767263381^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066416097 2500000000 33280767263381 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902624769/2000000000 : ℝ)^4539 ≤ (8948671589157/25000000000000 : ℝ)^3515 := by
    have hnat : (902624769 : ℕ)^4539*25000000000000^3515 ≤ 8948671589157^3515*2000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902624769 2000000000 8948671589157 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2014935223/5000000000 : ℝ)^4539 ≤ (30924546378059/100000000000000 : ℝ)^3515 := by
    have hnat : (2014935223 : ℕ)^4539*100000000000000^3515 ≤ 30924546378059^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014935223 5000000000 30924546378059 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1066416097/2500000000 : ℝ), (902624769/2000000000 : ℝ), (2014935223/5000000000 : ℝ)] ![(33280767263381/100000000000000 : ℝ), (8948671589157/25000000000000 : ℝ), (30924546378059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1066416097/2500000000 : ℝ)|^4539 ≤ (33280767263381/100000000000000 : ℝ)^3515
        have hw : |(1066416097/2500000000 : ℝ)|=(1066416097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902624769/2000000000 : ℝ)|^4539 ≤ (8948671589157/25000000000000 : ℝ)^3515
        have hw : |(902624769/2000000000 : ℝ)|=(902624769/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2014935223/5000000000 : ℝ)|^4539 ≤ (30924546378059/100000000000000 : ℝ)^3515
        have hw : |(2014935223/5000000000 : ℝ)|=(2014935223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1521_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    (219/2000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (219/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (219/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (219/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (219/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (219/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (219/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (219/2000 : ℝ) ^ (4537/1024 : ℝ) ≤ (5545831355627537/100000000000000000000 : ℝ) := by
    have hpowers : (219/2000 : ℝ)^4537 ≤ (5545831355627537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (219 : ℕ)^4537*100000000000000000000^1024 ≤ 5545831355627537^1024*2000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        219 2000 5545831355627537 100000000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (219/2000 : ℝ)) (X := (5545831355627537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4537/1024 : ℝ) ≤ (6435531953359231/25000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4537 ≤ (6435531953359231/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4537*25000000000000000000^1024 ≤ 6435531953359231^1024*25000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 6435531953359231 25000000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (6435531953359231/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005545831355627537/50000000000000000000 : ℝ) ≤ (2500062581964547/2500000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (50005545831355627537/50000000000000000000 : ℝ)^1024 ≤ (2500062581964547/2500000000000000 : ℝ)^4537 := by
      have hnat : (50005545831355627537 : ℕ)^1024*2500000000000000^4537 ≤ 2500062581964547^4537*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005545831355627537 50000000000000000000 2500062581964547 2500000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500062581964547/2500000000000000 : ℝ)) (X := (50005545831355627537/50000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031287959169064461/100000000000000000000 : ℝ) ≤ (10000706083094447/10000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (100031287959169064461/100000000000000000000 : ℝ)^1024 ≤ (10000706083094447/10000000000000000 : ℝ)^4537 := by
      have hnat : (100031287959169064461 : ℕ)^1024*10000000000000000^4537 ≤ 10000706083094447^4537*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031287959169064461 100000000000000000000 10000706083094447 10000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000706083094447/10000000000000000 : ℝ)) (X := (100031287959169064461/100000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506435531953359231/12500000000000000000 : ℝ) ≤ (5000580919165353/5000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (12506435531953359231/12500000000000000000 : ℝ)^1024 ≤ (5000580919165353/5000000000000000 : ℝ)^4537 := by
      have hnat : (12506435531953359231 : ℕ)^1024*5000000000000000^4537 ≤ 5000580919165353^4537*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506435531953359231 12500000000000000000 5000580919165353 5000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000580919165353/5000000000000000 : ℝ)) (X := (12506435531953359231/12500000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5545831355627537/100000000000000000000 : ℝ) ≤ ((11332788486708738073/11335000000000000000 : ℝ)+2*(455755236259/453400000000000 : ℝ)*(219/2000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (11332788486708738073/11335000000000000000 : ℝ)+2*(455755236259/453400000000000 : ℝ)*(219/2000 : ℝ)=(2500062581964547/2500000000000000 : ℝ) by norm_num, show 1+2*(5545831355627537/100000000000000000000 : ℝ)=(50005545831355627537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6435531953359231/25000000000000000000 : ℝ)+(5545831355627537/100000000000000000000 : ℝ) ≤ ((11332788486708738073/11335000000000000000 : ℝ)+(455755236259/453400000000000 : ℝ)*((3871/25000 : ℝ)+(219/2000 : ℝ)))^(4537/1024 : ℝ) := by
    rw [show (11332788486708738073/11335000000000000000 : ℝ)+(455755236259/453400000000000 : ℝ)*((3871/25000 : ℝ)+(219/2000 : ℝ))=(10000706083094447/10000000000000000 : ℝ) by norm_num, show 1+(6435531953359231/25000000000000000000 : ℝ)+(5545831355627537/100000000000000000000 : ℝ)=(100031287959169064461/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6435531953359231/25000000000000000000 : ℝ) ≤ ((11332788486708738073/11335000000000000000 : ℝ)+2*(455755236259/453400000000000 : ℝ)*(3871/25000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (11332788486708738073/11335000000000000000 : ℝ)+2*(455755236259/453400000000000 : ℝ)*(3871/25000 : ℝ)=(5000580919165353/5000000000000000 : ℝ) by norm_num, show 1+2*(6435531953359231/25000000000000000000 : ℝ)=(12506435531953359231/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11332788486708738073/11335000000000000000 : ℝ)*(X 1 0+X 2 0)+(455755236259/453400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (11332788486708738073/11335000000000000000 : ℝ)) (alpha := (455755236259/453400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11332788486708738073/11335000000000000000 : ℝ)*(X 0 1+X 2 1)+(455755236259/453400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (11332788486708738073/11335000000000000000 : ℝ)) (alpha := (455755236259/453400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11332788486708738073/11335000000000000000 : ℝ)*(X 0 2+X 1 2)+(455755236259/453400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (11332788486708738073/11335000000000000000 : ℝ)) (alpha := (455755236259/453400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1070217211/2000000000 : ℝ)*X 1 0+(-1964375749/10000000000 : ℝ)*X 1 1+(2609039409/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s6_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1854830697/10000000000 : ℝ)*X 0 0+(5219182809/10000000000 : ℝ)*X 0 1+(678869139/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647418521/5000000000 : ℝ)*X 1 0+(-1751501517/10000000000 : ℝ)*X 1 1+(1357738261/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2647418467/5000000000 : ℝ)*X 2 0+(1357738269/2500000000 : ℝ)*X 2 1+(-1751501621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1066416097/2500000000 : ℝ)*X 0 0+(902624769/2000000000 : ℝ)*X 0 1+(2014935223/5000000000 : ℝ)*X 0 2+(1066416097/2500000000 : ℝ)*X 1 0+(902624769/2000000000 : ℝ)*X 1 1+(2014935223/5000000000 : ℝ)*X 1 2+(1066416097/2500000000 : ℝ)*X 2 0+(902624769/2000000000 : ℝ)*X 2 1+(2014935223/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2198428775564987526644385573/283375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1217675289/100000000000000 : ℝ)*(base19) + (1149579379/100000000000000 : ℝ)*(base23) + (35849651/10000000000000 : ℝ)*(lower1) + (32875853/50000000000000 : ℝ)*(upper3) + (1034181/2500000000000 : ℝ)*(lower4) + (205887661/100000000000000 : ℝ)*(upper5) + (1697845406094167/50000000000000 : ℝ)*(major0) + (1697845406094167/50000000000000 : ℝ)*(major1) + (1697845406094167/50000000000000 : ℝ)*(major2) + (2348879393/50000000000000 : ℝ)*(sp0) + (2361041567734519/50000000000000 : ℝ)*(sp1) + (4722077220034963/100000000000000 : ℝ)*(sp2) + (2361040992944829/50000000000000 : ℝ)*(sp3) + (1034649115153487/50000000000000 : ℝ)*(sp4) + (1034649115153487/50000000000000 : ℝ)*(f.failure) + (2361041567734519/50000000000000 : ℝ)*(f.sum) + (39030387997457/11335000000000000000000000000 : ℝ)*base66 + (3123021836623554809/566750000000000000000000000000000 : ℝ)*base68 + (4995265662647554809/566750000000000000000000000000000 : ℝ)*base70 + (3211155891341554809/566750000000000000000000000000000 : ℝ)*base72 + (28283910433911/5667500000000000000000000000 : ℝ)*base74 + (1529887559419554809/566750000000000000000000000000000 : ℝ)*base76 + (1390174067600445191/566750000000000000000000000000000 : ℝ)*base77 + (5134344152620945191/566750000000000000000000000000000 : ℝ)*base79 + (48005127698057/11335000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (17101829/5000000000000000000000 : ℝ)*base89 + (17101829/5000000000000000000000 : ℝ)*base91 + (17101829/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1521_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1521_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1521_box_0 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-821385051/5000000000 : ℝ)*x 0 + (5401860723/10000000000 : ℝ)*x 1 + (5401861227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (821385051/5000000000 : ℝ)^4539 ≤ (9706358873257/100000000000000 : ℝ)^3515 := by
    have hnat : (821385051 : ℕ)^4539*100000000000000^3515 ≤ 9706358873257^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      821385051 5000000000 9706358873257 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401860723/10000000000 : ℝ)^4539 ≤ (45146817837829/100000000000000 : ℝ)^3515 := by
    have hnat : (5401860723 : ℕ)^4539*100000000000000^3515 ≤ 45146817837829^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401860723 10000000000 45146817837829 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401861227/10000000000 : ℝ)^4539 ≤ (22573411638603/50000000000000 : ℝ)^3515 := by
    have hnat : (5401861227 : ℕ)^4539*50000000000000^3515 ≤ 22573411638603^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401861227 10000000000 22573411638603 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-821385051/5000000000 : ℝ), (5401860723/10000000000 : ℝ), (5401861227/10000000000 : ℝ)] ![(9706358873257/100000000000000 : ℝ), (45146817837829/100000000000000 : ℝ), (22573411638603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-821385051/5000000000 : ℝ)|^4539 ≤ (9706358873257/100000000000000 : ℝ)^3515
        have hw : |(-821385051/5000000000 : ℝ)|=(821385051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401860723/10000000000 : ℝ)|^4539 ≤ (45146817837829/100000000000000 : ℝ)^3515
        have hw : |(5401860723/10000000000 : ℝ)|=(5401860723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401861227/10000000000 : ℝ)|^4539 ≤ (22573411638603/50000000000000 : ℝ)^3515
        have hw : |(5401861227/10000000000 : ℝ)|=(5401861227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_1 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635442061/5000000000 : ℝ)*x 0 + (-1824524937/10000000000 : ℝ)*x 1 + (540185981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635442061/5000000000 : ℝ)^4539 ≤ (21869142672567/50000000000000 : ℝ)^3515 := by
    have hnat : (2635442061 : ℕ)^4539*50000000000000^3515 ≤ 21869142672567^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635442061 5000000000 21869142672567 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1824524937/10000000000 : ℝ)^4539 ≤ (11114906667817/100000000000000 : ℝ)^3515 := by
    have hnat : (1824524937 : ℕ)^4539*100000000000000^3515 ≤ 11114906667817^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824524937 10000000000 11114906667817 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540185981/1000000000 : ℝ)^4539 ≤ (9029361596871/20000000000000 : ℝ)^3515 := by
    have hnat : (540185981 : ℕ)^4539*20000000000000^3515 ≤ 9029361596871^3515*1000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540185981 1000000000 9029361596871 20000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635442061/5000000000 : ℝ), (-1824524937/10000000000 : ℝ), (540185981/1000000000 : ℝ)] ![(21869142672567/50000000000000 : ℝ), (11114906667817/100000000000000 : ℝ), (9029361596871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635442061/5000000000 : ℝ)|^4539 ≤ (21869142672567/50000000000000 : ℝ)^3515
        have hw : |(2635442061/5000000000 : ℝ)|=(2635442061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1824524937/10000000000 : ℝ)|^4539 ≤ (11114906667817/100000000000000 : ℝ)^3515
        have hw : |(-1824524937/10000000000 : ℝ)|=(1824524937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540185981/1000000000 : ℝ)|^4539 ≤ (9029361596871/20000000000000 : ℝ)^3515
        have hw : |(540185981/1000000000 : ℝ)|=(540185981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_2 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635441933/5000000000 : ℝ)*x 0 + (2700929869/5000000000 : ℝ)*x 1 + (-1824525383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635441933/5000000000 : ℝ)^4539 ≤ (21869141300981/50000000000000 : ℝ)^3515 := by
    have hnat : (2635441933 : ℕ)^4539*50000000000000^3515 ≤ 21869141300981^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635441933 5000000000 21869141300981 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700929869/5000000000 : ℝ)^4539 ≤ (45146807207301/100000000000000 : ℝ)^3515 := by
    have hnat : (2700929869 : ℕ)^4539*100000000000000^3515 ≤ 45146807207301^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700929869 5000000000 45146807207301 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824525383/10000000000 : ℝ)^4539 ≤ (11114910176351/100000000000000 : ℝ)^3515 := by
    have hnat : (1824525383 : ℕ)^4539*100000000000000^3515 ≤ 11114910176351^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824525383 10000000000 11114910176351 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635441933/5000000000 : ℝ), (2700929869/5000000000 : ℝ), (-1824525383/10000000000 : ℝ)] ![(21869141300981/50000000000000 : ℝ), (45146807207301/100000000000000 : ℝ), (11114910176351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635441933/5000000000 : ℝ)|^4539 ≤ (21869141300981/50000000000000 : ℝ)^3515
        have hw : |(2635441933/5000000000 : ℝ)|=(2635441933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700929869/5000000000 : ℝ)|^4539 ≤ (45146807207301/100000000000000 : ℝ)^3515
        have hw : |(2700929869/5000000000 : ℝ)|=(2700929869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1824525383/10000000000 : ℝ)|^4539 ≤ (11114910176351/100000000000000 : ℝ)^3515
        have hw : |(-1824525383/10000000000 : ℝ)|=(1824525383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_3 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4468262981/10000000000 : ℝ)*x 0 + (834238433/2000000000 : ℝ)*x 1 + (4171191611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4468262981/10000000000 : ℝ)^4539 ≤ (35335897303713/100000000000000 : ℝ)^3515 := by
    have hnat : (4468262981 : ℕ)^4539*100000000000000^3515 ≤ 35335897303713^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4468262981 10000000000 35335897303713 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (834238433/2000000000 : ℝ)^4539 ≤ (8083013528729/25000000000000 : ℝ)^3515 := by
    have hnat : (834238433 : ℕ)^4539*25000000000000^3515 ≤ 8083013528729^3515*2000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834238433 2000000000 8083013528729 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171191611/10000000000 : ℝ)^4539 ≤ (3233204856971/10000000000000 : ℝ)^3515 := by
    have hnat : (4171191611 : ℕ)^4539*10000000000000^3515 ≤ 3233204856971^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171191611 10000000000 3233204856971 10000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4468262981/10000000000 : ℝ), (834238433/2000000000 : ℝ), (4171191611/10000000000 : ℝ)] ![(35335897303713/100000000000000 : ℝ), (8083013528729/25000000000000 : ℝ), (3233204856971/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4468262981/10000000000 : ℝ)|^4539 ≤ (35335897303713/100000000000000 : ℝ)^3515
        have hw : |(4468262981/10000000000 : ℝ)|=(4468262981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(834238433/2000000000 : ℝ)|^4539 ≤ (8083013528729/25000000000000 : ℝ)^3515
        have hw : |(834238433/2000000000 : ℝ)|=(834238433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171191611/10000000000 : ℝ)|^4539 ≤ (3233204856971/10000000000000 : ℝ)^3515
        have hw : |(4171191611/10000000000 : ℝ)|=(4171191611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_4 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2072268979/10000000000 : ℝ)*x 0 + (2621952693/5000000000 : ℝ)*x 1 + (1310975771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2072268979/10000000000 : ℝ)^4539 ≤ (524048182343/4000000000000 : ℝ)^3515 := by
    have hnat : (2072268979 : ℕ)^4539*4000000000000^3515 ≤ 524048182343^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072268979 10000000000 524048182343 4000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621952693/5000000000 : ℝ)^4539 ≤ (1086235250777/2500000000000 : ℝ)^3515 := by
    have hnat : (2621952693 : ℕ)^4539*2500000000000^3515 ≤ 1086235250777^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621952693 5000000000 1086235250777 2500000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310975771/2500000000 : ℝ)^4539 ≤ (4344938540081/10000000000000 : ℝ)^3515 := by
    have hnat : (1310975771 : ℕ)^4539*10000000000000^3515 ≤ 4344938540081^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310975771 2500000000 4344938540081 10000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2072268979/10000000000 : ℝ), (2621952693/5000000000 : ℝ), (1310975771/2500000000 : ℝ)] ![(524048182343/4000000000000 : ℝ), (1086235250777/2500000000000 : ℝ), (4344938540081/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2072268979/10000000000 : ℝ)|^4539 ≤ (524048182343/4000000000000 : ℝ)^3515
        have hw : |(-2072268979/10000000000 : ℝ)|=(2072268979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621952693/5000000000 : ℝ)|^4539 ≤ (1086235250777/2500000000000 : ℝ)^3515
        have hw : |(2621952693/5000000000 : ℝ)|=(2621952693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310975771/2500000000 : ℝ)|^4539 ≤ (4344938540081/10000000000000 : ℝ)^3515
        have hw : |(1310975771/2500000000 : ℝ)|=(1310975771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_5 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380778679/10000000000 : ℝ)*x 0 + (-1889814499/10000000000 : ℝ)*x 1 + (1310976251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380778679/10000000000 : ℝ)^4539 ≤ (44919421144303/100000000000000 : ℝ)^3515 := by
    have hnat : (5380778679 : ℕ)^4539*100000000000000^3515 ≤ 44919421144303^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380778679 10000000000 44919421144303 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1889814499/10000000000 : ℝ)^4539 ≤ (5815586447487/50000000000000 : ℝ)^3515 := by
    have hnat : (1889814499 : ℕ)^4539*50000000000000^3515 ≤ 5815586447487^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1889814499 10000000000 5815586447487 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310976251/2500000000 : ℝ)^4539 ≤ (10862351485967/25000000000000 : ℝ)^3515 := by
    have hnat : (1310976251 : ℕ)^4539*25000000000000^3515 ≤ 10862351485967^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310976251 2500000000 10862351485967 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380778679/10000000000 : ℝ), (-1889814499/10000000000 : ℝ), (1310976251/2500000000 : ℝ)] ![(44919421144303/100000000000000 : ℝ), (5815586447487/50000000000000 : ℝ), (10862351485967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380778679/10000000000 : ℝ)|^4539 ≤ (44919421144303/100000000000000 : ℝ)^3515
        have hw : |(5380778679/10000000000 : ℝ)|=(5380778679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1889814499/10000000000 : ℝ)|^4539 ≤ (5815586447487/50000000000000 : ℝ)^3515
        have hw : |(-1889814499/10000000000 : ℝ)|=(1889814499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310976251/2500000000 : ℝ)|^4539 ≤ (10862351485967/25000000000000 : ℝ)^3515
        have hw : |(1310976251/2500000000 : ℝ)|=(1310976251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_6 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380780459/10000000000 : ℝ)*x 0 + (5243903039/10000000000 : ℝ)*x 1 + (-188981473/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380780459/10000000000 : ℝ)^4539 ≤ (4491944033293/10000000000000 : ℝ)^3515 := by
    have hnat : (5380780459 : ℕ)^4539*10000000000000^3515 ≤ 4491944033293^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380780459 10000000000 4491944033293 10000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243903039/10000000000 : ℝ)^4539 ≤ (10862346229833/25000000000000 : ℝ)^3515 := by
    have hnat : (5243903039 : ℕ)^4539*25000000000000^3515 ≤ 10862346229833^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243903039 10000000000 10862346229833 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188981473/1000000000 : ℝ)^4539 ≤ (11631174730883/100000000000000 : ℝ)^3515 := by
    have hnat : (188981473 : ℕ)^4539*100000000000000^3515 ≤ 11631174730883^3515*1000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188981473 1000000000 11631174730883 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380780459/10000000000 : ℝ), (5243903039/10000000000 : ℝ), (-188981473/1000000000 : ℝ)] ![(4491944033293/10000000000000 : ℝ), (10862346229833/25000000000000 : ℝ), (11631174730883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380780459/10000000000 : ℝ)|^4539 ≤ (4491944033293/10000000000000 : ℝ)^3515
        have hw : |(5380780459/10000000000 : ℝ)|=(5380780459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243903039/10000000000 : ℝ)|^4539 ≤ (10862346229833/25000000000000 : ℝ)^3515
        have hw : |(5243903039/10000000000 : ℝ)|=(5243903039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188981473/1000000000 : ℝ)|^4539 ≤ (11631174730883/100000000000000 : ℝ)^3515
        have hw : |(-188981473/1000000000 : ℝ)|=(188981473/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_7 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2030236511/5000000000 : ℝ)*x 0 + (4374953823/10000000000 : ℝ)*x 1 + (546869203/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030236511/5000000000 : ℝ)^4539 ≤ (7807033552459/25000000000000 : ℝ)^3515 := by
    have hnat : (2030236511 : ℕ)^4539*25000000000000^3515 ≤ 7807033552459^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030236511 5000000000 7807033552459 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4374953823/10000000000 : ℝ)^4539 ≤ (1074560434173/3125000000000 : ℝ)^3515 := by
    have hnat : (4374953823 : ℕ)^4539*3125000000000^3515 ≤ 1074560434173^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374953823 10000000000 1074560434173 3125000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546869203/1250000000 : ℝ)^4539 ≤ (34385931873797/100000000000000 : ℝ)^3515 := by
    have hnat : (546869203 : ℕ)^4539*100000000000000^3515 ≤ 34385931873797^3515*1250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546869203 1250000000 34385931873797 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2030236511/5000000000 : ℝ), (4374953823/10000000000 : ℝ), (546869203/1250000000 : ℝ)] ![(7807033552459/25000000000000 : ℝ), (1074560434173/3125000000000 : ℝ), (34385931873797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2030236511/5000000000 : ℝ)|^4539 ≤ (7807033552459/25000000000000 : ℝ)^3515
        have hw : |(2030236511/5000000000 : ℝ)|=(2030236511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4374953823/10000000000 : ℝ)|^4539 ≤ (1074560434173/3125000000000 : ℝ)^3515
        have hw : |(4374953823/10000000000 : ℝ)|=(4374953823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546869203/1250000000 : ℝ)|^4539 ≤ (34385931873797/100000000000000 : ℝ)^3515
        have hw : |(546869203/1250000000 : ℝ)|=(546869203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_8 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1981458853/10000000000 : ℝ)*x 0 + (5133145059/10000000000 : ℝ)*x 1 + (5422287067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1981458853/10000000000 : ℝ)^4539 ≤ (12364618050181/100000000000000 : ℝ)^3515 := by
    have hnat : (1981458853 : ℕ)^4539*100000000000000^3515 ≤ 12364618050181^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981458853 10000000000 12364618050181 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133145059/10000000000 : ℝ)^4539 ≤ (2641749575369/6250000000000 : ℝ)^3515 := by
    have hnat : (5133145059 : ℕ)^4539*6250000000000^3515 ≤ 2641749575369^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133145059 10000000000 2641749575369 6250000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422287067/10000000000 : ℝ)^4539 ≤ (1417730897597/3125000000000 : ℝ)^3515 := by
    have hnat : (5422287067 : ℕ)^4539*3125000000000^3515 ≤ 1417730897597^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422287067 10000000000 1417730897597 3125000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1981458853/10000000000 : ℝ), (5133145059/10000000000 : ℝ), (5422287067/10000000000 : ℝ)] ![(12364618050181/100000000000000 : ℝ), (2641749575369/6250000000000 : ℝ), (1417730897597/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1981458853/10000000000 : ℝ)|^4539 ≤ (12364618050181/100000000000000 : ℝ)^3515
        have hw : |(-1981458853/10000000000 : ℝ)|=(1981458853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133145059/10000000000 : ℝ)|^4539 ≤ (2641749575369/6250000000000 : ℝ)^3515
        have hw : |(5133145059/10000000000 : ℝ)|=(5133145059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422287067/10000000000 : ℝ)|^4539 ≤ (1417730897597/3125000000000 : ℝ)^3515
        have hw : |(5422287067/10000000000 : ℝ)|=(5422287067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_9 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256666191/10000000000 : ℝ)*x 0 + (-1815838031/10000000000 : ℝ)*x 1 + (5422287197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256666191/10000000000 : ℝ)^4539 ≤ (21792996380173/50000000000000 : ℝ)^3515 := by
    have hnat : (5256666191 : ℕ)^4539*50000000000000^3515 ≤ 21792996380173^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256666191 10000000000 21792996380173 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1815838031/10000000000 : ℝ)^4539 ≤ (172603392209/1562500000000 : ℝ)^3515 := by
    have hnat : (1815838031 : ℕ)^4539*1562500000000^3515 ≤ 172603392209^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815838031 10000000000 172603392209 1562500000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422287197/10000000000 : ℝ)^4539 ≤ (45367390127661/100000000000000 : ℝ)^3515 := by
    have hnat : (5422287197 : ℕ)^4539*100000000000000^3515 ≤ 45367390127661^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422287197 10000000000 45367390127661 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256666191/10000000000 : ℝ), (-1815838031/10000000000 : ℝ), (5422287197/10000000000 : ℝ)] ![(21792996380173/50000000000000 : ℝ), (172603392209/1562500000000 : ℝ), (45367390127661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256666191/10000000000 : ℝ)|^4539 ≤ (21792996380173/50000000000000 : ℝ)^3515
        have hw : |(5256666191/10000000000 : ℝ)|=(5256666191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1815838031/10000000000 : ℝ)|^4539 ≤ (172603392209/1562500000000 : ℝ)^3515
        have hw : |(-1815838031/10000000000 : ℝ)|=(1815838031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422287197/10000000000 : ℝ)|^4539 ≤ (45367390127661/100000000000000 : ℝ)^3515
        have hw : |(5422287197/10000000000 : ℝ)|=(5422287197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_10 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628333093/5000000000 : ℝ)*x 0 + (5422287103/10000000000 : ℝ)*x 1 + (-1815838167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628333093/5000000000 : ℝ)^4539 ≤ (43585992706811/100000000000000 : ℝ)^3515 := by
    have hnat : (2628333093 : ℕ)^4539*100000000000000^3515 ≤ 43585992706811^3515*5000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628333093 5000000000 43585992706811 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5422287103/10000000000 : ℝ)^4539 ≤ (22683694556029/50000000000000 : ℝ)^3515 := by
    have hnat : (5422287103 : ℕ)^4539*50000000000000^3515 ≤ 22683694556029^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422287103 10000000000 22683694556029 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1815838167/10000000000 : ℝ)^4539 ≤ (11046618169757/100000000000000 : ℝ)^3515 := by
    have hnat : (1815838167 : ℕ)^4539*100000000000000^3515 ≤ 11046618169757^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1815838167 10000000000 11046618169757 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628333093/5000000000 : ℝ), (5422287103/10000000000 : ℝ), (-1815838167/10000000000 : ℝ)] ![(43585992706811/100000000000000 : ℝ), (22683694556029/50000000000000 : ℝ), (11046618169757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628333093/5000000000 : ℝ)|^4539 ≤ (43585992706811/100000000000000 : ℝ)^3515
        have hw : |(2628333093/5000000000 : ℝ)|=(2628333093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5422287103/10000000000 : ℝ)|^4539 ≤ (22683694556029/50000000000000 : ℝ)^3515
        have hw : |(5422287103/10000000000 : ℝ)|=(5422287103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1815838167/10000000000 : ℝ)|^4539 ≤ (11046618169757/100000000000000 : ℝ)^3515
        have hw : |(-1815838167/10000000000 : ℝ)|=(1815838167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_11 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (903969107/2000000000 : ℝ)*x 0 + (4144809983/10000000000 : ℝ)*x 1 + (4144810033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903969107/2000000000 : ℝ)^4539 ≤ (8965885867673/25000000000000 : ℝ)^3515 := by
    have hnat : (903969107 : ℕ)^4539*25000000000000^3515 ≤ 8965885867673^3515*2000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903969107 2000000000 8965885867673 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144809983/10000000000 : ℝ)^4539 ≤ (16034114003703/50000000000000 : ℝ)^3515 := by
    have hnat : (4144809983 : ℕ)^4539*50000000000000^3515 ≤ 16034114003703^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144809983 10000000000 16034114003703 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4144810033/10000000000 : ℝ)^4539 ≤ (4008528563369/12500000000000 : ℝ)^3515 := by
    have hnat : (4144810033 : ℕ)^4539*12500000000000^3515 ≤ 4008528563369^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144810033 10000000000 4008528563369 12500000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(903969107/2000000000 : ℝ), (4144809983/10000000000 : ℝ), (4144810033/10000000000 : ℝ)] ![(8965885867673/25000000000000 : ℝ), (16034114003703/50000000000000 : ℝ), (4008528563369/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(903969107/2000000000 : ℝ)|^4539 ≤ (8965885867673/25000000000000 : ℝ)^3515
        have hw : |(903969107/2000000000 : ℝ)|=(903969107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144809983/10000000000 : ℝ)|^4539 ≤ (16034114003703/50000000000000 : ℝ)^3515
        have hw : |(4144809983/10000000000 : ℝ)|=(4144809983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4144810033/10000000000 : ℝ)|^4539 ≤ (4008528563369/12500000000000 : ℝ)^3515
        have hw : |(4144810033/10000000000 : ℝ)|=(4144810033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_12 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1733482219/10000000000 : ℝ)*x 0 + (5509090061/10000000000 : ℝ)*x 1 + (1307217733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1733482219/10000000000 : ℝ)^4539 ≤ (1300496515271/12500000000000 : ℝ)^3515 := by
    have hnat : (1733482219 : ℕ)^4539*12500000000000^3515 ≤ 1300496515271^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733482219 10000000000 1300496515271 12500000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509090061/10000000000 : ℝ)^4539 ≤ (46307411900649/100000000000000 : ℝ)^3515 := by
    have hnat : (5509090061 : ℕ)^4539*100000000000000^3515 ≤ 46307411900649^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509090061 10000000000 46307411900649 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307217733/2500000000 : ℝ)^4539 ≤ (21644307981823/50000000000000 : ℝ)^3515 := by
    have hnat : (1307217733 : ℕ)^4539*50000000000000^3515 ≤ 21644307981823^3515*2500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307217733 2500000000 21644307981823 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1733482219/10000000000 : ℝ), (5509090061/10000000000 : ℝ), (1307217733/2500000000 : ℝ)] ![(1300496515271/12500000000000 : ℝ), (46307411900649/100000000000000 : ℝ), (21644307981823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1733482219/10000000000 : ℝ)|^4539 ≤ (1300496515271/12500000000000 : ℝ)^3515
        have hw : |(-1733482219/10000000000 : ℝ)|=(1733482219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509090061/10000000000 : ℝ)|^4539 ≤ (46307411900649/100000000000000 : ℝ)^3515
        have hw : |(5509090061/10000000000 : ℝ)|=(5509090061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307217733/2500000000 : ℝ)|^4539 ≤ (21644307981823/50000000000000 : ℝ)^3515
        have hw : |(1307217733/2500000000 : ℝ)|=(1307217733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_13 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (673904887/1250000000 : ℝ)*x 0 + (-1895850427/10000000000 : ℝ)*x 1 + (5228870899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (673904887/1250000000 : ℝ)^4539 ≤ (5629027210567/12500000000000 : ℝ)^3515 := by
    have hnat : (673904887 : ℕ)^4539*12500000000000^3515 ≤ 5629027210567^3515*1250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673904887 1250000000 5629027210567 12500000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895850427/10000000000 : ℝ)^4539 ≤ (11679166689443/100000000000000 : ℝ)^3515 := by
    have hnat : (1895850427 : ℕ)^4539*100000000000000^3515 ≤ 11679166689443^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895850427 10000000000 11679166689443 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228870899/10000000000 : ℝ)^4539 ≤ (43288615610857/100000000000000 : ℝ)^3515 := by
    have hnat : (5228870899 : ℕ)^4539*100000000000000^3515 ≤ 43288615610857^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228870899 10000000000 43288615610857 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(673904887/1250000000 : ℝ), (-1895850427/10000000000 : ℝ), (5228870899/10000000000 : ℝ)] ![(5629027210567/12500000000000 : ℝ), (11679166689443/100000000000000 : ℝ), (43288615610857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(673904887/1250000000 : ℝ)|^4539 ≤ (5629027210567/12500000000000 : ℝ)^3515
        have hw : |(673904887/1250000000 : ℝ)|=(673904887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895850427/10000000000 : ℝ)|^4539 ≤ (11679166689443/100000000000000 : ℝ)^3515
        have hw : |(-1895850427/10000000000 : ℝ)|=(1895850427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228870899/10000000000 : ℝ)|^4539 ≤ (43288615610857/100000000000000 : ℝ)^3515
        have hw : |(5228870899/10000000000 : ℝ)|=(5228870899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_14 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215649563/400000000 : ℝ)*x 0 + (209154837/400000000 : ℝ)*x 1 + (-94792521/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215649563/400000000 : ℝ)^4539 ≤ (1801288698321/4000000000000 : ℝ)^3515 := by
    have hnat : (215649563 : ℕ)^4539*4000000000000^3515 ≤ 1801288698321^3515*400000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215649563 400000000 1801288698321 4000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209154837/400000000 : ℝ)^4539 ≤ (10822153972203/25000000000000 : ℝ)^3515 := by
    have hnat : (209154837 : ℕ)^4539*25000000000000^3515 ≤ 10822153972203^3515*400000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209154837 400000000 10822153972203 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94792521/500000000 : ℝ)^4539 ≤ (5839583316879/50000000000000 : ℝ)^3515 := by
    have hnat : (94792521 : ℕ)^4539*50000000000000^3515 ≤ 5839583316879^3515*500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94792521 500000000 5839583316879 50000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215649563/400000000 : ℝ), (209154837/400000000 : ℝ), (-94792521/500000000 : ℝ)] ![(1801288698321/4000000000000 : ℝ), (10822153972203/25000000000000 : ℝ), (5839583316879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215649563/400000000 : ℝ)|^4539 ≤ (1801288698321/4000000000000 : ℝ)^3515
        have hw : |(215649563/400000000 : ℝ)|=(215649563/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209154837/400000000 : ℝ)|^4539 ≤ (10822153972203/25000000000000 : ℝ)^3515
        have hw : |(209154837/400000000 : ℝ)|=(209154837/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94792521/500000000 : ℝ)|^4539 ≤ (5839583316879/50000000000000 : ℝ)^3515
        have hw : |(-94792521/500000000 : ℝ)|=(94792521/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1521_box_15 (p : ℝ) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (100520023/250000000 : ℝ)*x 0 + (4394323199/10000000000 : ℝ)*x 1 + (219716159/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100520023/250000000 : ℝ)^4539 ≤ (30834702347591/100000000000000 : ℝ)^3515 := by
    have hnat : (100520023 : ℕ)^4539*100000000000000^3515 ≤ 30834702347591^3515*250000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100520023 250000000 30834702347591 100000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4394323199/10000000000 : ℝ)^4539 ≤ (1729132445739/5000000000000 : ℝ)^3515 := by
    have hnat : (4394323199 : ℕ)^4539*5000000000000^3515 ≤ 1729132445739^3515*10000000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4394323199 10000000000 1729132445739 5000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219716159/500000000 : ℝ)^4539 ≤ (8645662180423/25000000000000 : ℝ)^3515 := by
    have hnat : (219716159 : ℕ)^4539*25000000000000^3515 ≤ 8645662180423^3515*500000000^4539 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219716159 500000000 8645662180423 25000000000000 4539 3515 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4539/1024 : ℝ)) 4539 3515 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100520023/250000000 : ℝ), (4394323199/10000000000 : ℝ), (219716159/500000000 : ℝ)] ![(30834702347591/100000000000000 : ℝ), (1729132445739/5000000000000 : ℝ), (8645662180423/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100520023/250000000 : ℝ)|^4539 ≤ (30834702347591/100000000000000 : ℝ)^3515
        have hw : |(100520023/250000000 : ℝ)|=(100520023/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4394323199/10000000000 : ℝ)|^4539 ≤ (1729132445739/5000000000000 : ℝ)^3515
        have hw : |(4394323199/10000000000 : ℝ)|=(4394323199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219716159/500000000 : ℝ)|^4539 ≤ (8645662180423/25000000000000 : ℝ)^3515
        have hw : |(219716159/500000000 : ℝ)|=(219716159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1521_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63751/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5867/10000 : ℝ) ∧ (16083/20000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (4303/5000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (219/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (219/2000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (219/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15483/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (219/2000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (219/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15483/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (219/2000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (219/2000 : ℝ) ^ (4537/1024 : ℝ) ≤ (5545831355627537/100000000000000000000 : ℝ) := by
    have hpowers : (219/2000 : ℝ)^4537 ≤ (5545831355627537/100000000000000000000 : ℝ)^1024 := by
      have hnat : (219 : ℕ)^4537*100000000000000000000^1024 ≤ 5545831355627537^1024*2000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        219 2000 5545831355627537 100000000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (219/2000 : ℝ)) (X := (5545831355627537/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15483/100000 : ℝ) ^ (4537/1024 : ℝ) ≤ (321684533209353/1250000000000000000 : ℝ) := by
    have hpowers : (15483/100000 : ℝ)^4537 ≤ (321684533209353/1250000000000000000 : ℝ)^1024 := by
      have hnat : (15483 : ℕ)^4537*1250000000000000000^1024 ≤ 321684533209353^1024*100000^4537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15483 100000 321684533209353 1250000000000000000 4537 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15483/100000 : ℝ)) (X := (321684533209353/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005545831355627537/50000000000000000000 : ℝ) ≤ (2500062581964547/2500000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (50005545831355627537/50000000000000000000 : ℝ)^1024 ≤ (2500062581964547/2500000000000000 : ℝ)^4537 := by
      have hnat : (50005545831355627537 : ℕ)^1024*2500000000000000^4537 ≤ 2500062581964547^4537*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005545831355627537 50000000000000000000 2500062581964547 2500000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500062581964547/2500000000000000 : ℝ)) (X := (50005545831355627537/50000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100031280594012375777/100000000000000000000 : ℝ) ≤ (5000352958451631/5000000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (100031280594012375777/100000000000000000000 : ℝ)^1024 ≤ (5000352958451631/5000000000000000 : ℝ)^4537 := by
      have hnat : (100031280594012375777 : ℕ)^1024*5000000000000000^4537 ≤ 5000352958451631^4537*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100031280594012375777 100000000000000000000 5000352958451631 5000000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000352958451631/5000000000000000 : ℝ)) (X := (100031280594012375777/100000000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (625321684533209353/625000000000000000 : ℝ) ≤ (625072594121771/625000000000000 : ℝ) ^ (4537/1024 : ℝ) := by
    have hpowers : (625321684533209353/625000000000000000 : ℝ)^1024 ≤ (625072594121771/625000000000000 : ℝ)^4537 := by
      have hnat : (625321684533209353 : ℕ)^1024*625000000000000^4537 ≤ 625072594121771^4537*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625321684533209353 625000000000000000 625072594121771 625000000000000 1024 4537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625072594121771/625000000000000 : ℝ)) (X := (625321684533209353/625000000000000000 : ℝ)) (by norm_num) 4537 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5545831355627537/100000000000000000000 : ℝ) ≤ ((3776763111341170467/3777500000000000000 : ℝ)+2*(227794522537/226650000000000 : ℝ)*(219/2000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (3776763111341170467/3777500000000000000 : ℝ)+2*(227794522537/226650000000000 : ℝ)*(219/2000 : ℝ)=(2500062581964547/2500000000000000 : ℝ) by norm_num, show 1+2*(5545831355627537/100000000000000000000 : ℝ)=(50005545831355627537/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(321684533209353/1250000000000000000 : ℝ)+(5545831355627537/100000000000000000000 : ℝ) ≤ ((3776763111341170467/3777500000000000000 : ℝ)+(227794522537/226650000000000 : ℝ)*((15483/100000 : ℝ)+(219/2000 : ℝ)))^(4537/1024 : ℝ) := by
    rw [show (3776763111341170467/3777500000000000000 : ℝ)+(227794522537/226650000000000 : ℝ)*((15483/100000 : ℝ)+(219/2000 : ℝ))=(5000352958451631/5000000000000000 : ℝ) by norm_num, show 1+(321684533209353/1250000000000000000 : ℝ)+(5545831355627537/100000000000000000000 : ℝ)=(100031280594012375777/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(321684533209353/1250000000000000000 : ℝ) ≤ ((3776763111341170467/3777500000000000000 : ℝ)+2*(227794522537/226650000000000 : ℝ)*(15483/100000 : ℝ))^(4537/1024 : ℝ) := by
    rw [show (3776763111341170467/3777500000000000000 : ℝ)+2*(227794522537/226650000000000 : ℝ)*(15483/100000 : ℝ)=(625072594121771/625000000000000 : ℝ) by norm_num, show 1+2*(321684533209353/1250000000000000000 : ℝ)=(625321684533209353/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3776763111341170467/3777500000000000000 : ℝ)*(X 1 0+X 2 0)+(227794522537/226650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3776763111341170467/3777500000000000000 : ℝ)) (alpha := (227794522537/226650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3776763111341170467/3777500000000000000 : ℝ)*(X 0 1+X 2 1)+(227794522537/226650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3776763111341170467/3777500000000000000 : ℝ)) (alpha := (227794522537/226650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3776763111341170467/3777500000000000000 : ℝ)*(X 0 2+X 1 2)+(227794522537/226650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4537/1024 : ℝ)) (lo := (219/2000 : ℝ)) (hi := (15483/100000 : ℝ)) (c := (3776763111341170467/3777500000000000000 : ℝ)) (alpha := (227794522537/226650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-821385051/5000000000 : ℝ)*X 0 0+(5401860723/10000000000 : ℝ)*X 0 1+(5401861227/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635442061/5000000000 : ℝ)*X 1 0+(-1824524937/10000000000 : ℝ)*X 1 1+(540185981/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635441933/5000000000 : ℝ)*X 2 0+(2700929869/5000000000 : ℝ)*X 2 1+(-1824525383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4468262981/10000000000 : ℝ)*X 0 0+(834238433/2000000000 : ℝ)*X 0 1+(4171191611/10000000000 : ℝ)*X 0 2+(4468262981/10000000000 : ℝ)*X 1 0+(834238433/2000000000 : ℝ)*X 1 1+(4171191611/10000000000 : ℝ)*X 1 2+(4468262981/10000000000 : ℝ)*X 2 0+(834238433/2000000000 : ℝ)*X 2 1+(4171191611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2072268979/10000000000 : ℝ)*X 0 0+(2621952693/5000000000 : ℝ)*X 0 1+(1310975771/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5380778679/10000000000 : ℝ)*X 1 0+(-1889814499/10000000000 : ℝ)*X 1 1+(1310976251/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5380780459/10000000000 : ℝ)*X 2 0+(5243903039/10000000000 : ℝ)*X 2 1+(-188981473/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2030236511/5000000000 : ℝ)*X 0 0+(4374953823/10000000000 : ℝ)*X 0 1+(546869203/1250000000 : ℝ)*X 0 2+(2030236511/5000000000 : ℝ)*X 1 0+(4374953823/10000000000 : ℝ)*X 1 1+(546869203/1250000000 : ℝ)*X 1 2+(2030236511/5000000000 : ℝ)*X 2 0+(4374953823/10000000000 : ℝ)*X 2 1+(546869203/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1981458853/10000000000 : ℝ)*X 0 0+(5133145059/10000000000 : ℝ)*X 0 1+(5422287067/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256666191/10000000000 : ℝ)*X 1 0+(-1815838031/10000000000 : ℝ)*X 1 1+(5422287197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2628333093/5000000000 : ℝ)*X 2 0+(5422287103/10000000000 : ℝ)*X 2 1+(-1815838167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((903969107/2000000000 : ℝ)*X 0 0+(4144809983/10000000000 : ℝ)*X 0 1+(4144810033/10000000000 : ℝ)*X 0 2+(903969107/2000000000 : ℝ)*X 1 0+(4144809983/10000000000 : ℝ)*X 1 1+(4144810033/10000000000 : ℝ)*X 1 2+(903969107/2000000000 : ℝ)*X 2 0+(4144809983/10000000000 : ℝ)*X 2 1+(4144810033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1733482219/10000000000 : ℝ)*X 0 0+(5509090061/10000000000 : ℝ)*X 0 1+(1307217733/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((673904887/1250000000 : ℝ)*X 1 0+(-1895850427/10000000000 : ℝ)*X 1 1+(5228870899/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215649563/400000000 : ℝ)*X 2 0+(209154837/400000000 : ℝ)*X 2 1+(-94792521/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((100520023/250000000 : ℝ)*X 0 0+(4394323199/10000000000 : ℝ)*X 0 1+(219716159/500000000 : ℝ)*X 0 2+(100520023/250000000 : ℝ)*X 1 0+(4394323199/10000000000 : ℝ)*X 1 1+(219716159/500000000 : ℝ)*X 1 2+(100520023/250000000 : ℝ)*X 2 0+(4394323199/10000000000 : ℝ)*X 2 1+(219716159/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1521_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63751/100000 : ℝ) ≤ (-12040581207538930110291303114107/18887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35963191/25000000000000 : ℝ)*(upper1) + (92520249/100000000000000 : ℝ)*(upper4) + (320029883/100000000000000 : ℝ)*(upper5) + (223666270804769/10000000000000 : ℝ)*(major0) + (223666270804769/10000000000000 : ℝ)*(major1) + (223666270804769/10000000000000 : ℝ)*(major2) + (19670441929/50000000000000 : ℝ)*(sp2) + (9145469009/100000000000000 : ℝ)*(sp3) + (3131537209724697/100000000000000 : ℝ)*(sp4) + (78288630811861/2500000000000 : ℝ)*(sp5) + (626307403200441/20000000000000 : ℝ)*(sp6) + (170373695087279/12500000000000 : ℝ)*(sp7) + (19573580683/50000000000000 : ℝ)*(sp8) + (15562205811/50000000000000 : ℝ)*(sp13) + (1362998706167241/100000000000000 : ℝ)*(f.failure) + (1565788178443031/50000000000000 : ℝ)*(f.sum) + (659482879433/566625000000000000000000000 : ℝ)*base66 + (907603888704796369/113325000000000000000000000000000 : ℝ)*base67 + (960341798898796369/113325000000000000000000000000000 : ℝ)*base69 + (869070289492696369/113325000000000000000000000000000 : ℝ)*base71 + (12563840534501/4533000000000000000000000000 : ℝ)*base73 + (962816038582696369/113325000000000000000000000000000 : ℝ)*base75 + (348986886618121369/113325000000000000000000000000000 : ℝ)*base77 + (413461381577821369/113325000000000000000000000000000 : ℝ)*base79 + (12753606954787/4533000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (72832253/10000000000000000000000 : ℝ)*base90 + (72832253/10000000000000000000000 : ℝ)*base92 + (72832253/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5867/10000 : ℝ) ≤ (27704426106790331789291569332333/47218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13242597/10000000000000 : ℝ)*(lower0) + (38940013/25000000000000 : ℝ)*(upper2) + (43129291/100000000000000 : ℝ)*(lower5) + (1156750190122383/50000000000000 : ℝ)*(major0) + (1156750190122383/50000000000000 : ℝ)*(major1) + (1156750190122383/50000000000000 : ℝ)*(major2) + (639522990014163/20000000000000 : ℝ)*(sp0) + (1598722760456047/50000000000000 : ℝ)*(sp1) + (3197393539605013/100000000000000 : ℝ)*(sp2) + (704910180004193/50000000000000 : ℝ)*(sp3) + (37728601/1562500000000 : ℝ)*(sp7) + (87480699853/50000000000000 : ℝ)*(sp9) + (226942706787/100000000000000 : ℝ)*(sp10) + (1106448197/20000000000000 : ℝ)*(sp12) + (28196455492777/2000000000000 : ℝ)*(f.failure) + (15988102411559/500000000000 : ℝ)*(f.sum) + (36686110965133/7555000000000000000000000000 : ℝ)*base65 + (1640600796853387139/188875000000000000000000000000000 : ℝ)*base68 + (1036461541624012139/188875000000000000000000000000000 : ℝ)*base70 + (83411805614612861/188875000000000000000000000000000 : ℝ)*base71 + (20158246591831/3777500000000000000000000000 : ℝ)*base74 + (739279609832387139/188875000000000000000000000000000 : ℝ)*base76 + (252807098833637139/188875000000000000000000000000000 : ℝ)*base78 + (2031739262612762139/188875000000000000000000000000000 : ℝ)*base80 + (3317072647171/3777500000000000000000000000 : ℝ)*base82 + (1828259/200000000000000000000 : ℝ)*base89 + (1828259/200000000000000000000 : ℝ)*base91 + (1828259/200000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (16083/20000 : ℝ) ≤ (37972340440138348629860375773869/47218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1129/5000000000000 : ℝ)*(upper1) + (34905859/100000000000000 : ℝ)*(upper2) + (19107633/100000000000000 : ℝ)*(lower5) + (626580036963519/25000000000000 : ℝ)*(major0) + (626580036963519/25000000000000 : ℝ)*(major1) + (626580036963519/25000000000000 : ℝ)*(major2) + (2067035557/5000000000000 : ℝ)*(sp1) + (9003344323/50000000000000 : ℝ)*(sp2) + (9958205509/100000000000000 : ℝ)*(sp3) + (2212366273/100000000000000 : ℝ)*(sp4) + (432313374541259/12500000000000 : ℝ)*(sp8) + (1729233933992603/50000000000000 : ℝ)*(sp9) + (34584912020077/1000000000000 : ℝ)*(sp10) + (61092606110483/4000000000000 : ℝ)*(sp11) + (47728909717737/3125000000000 : ℝ)*(f.failure) + (1729254604348173/50000000000000 : ℝ)*(f.sum) + (37175217187697/7555000000000000000000000000 : ℝ)*base66 + (474628898853243373/94437500000000000000000000000000 : ℝ)*base67 + (172555832863618373/94437500000000000000000000000000 : ℝ)*base69 + (9443045270756627/94437500000000000000000000000000 : ℝ)*base72 + (3870426987589/944375000000000000000000000 : ℝ)*base74 + (287678356354256627/94437500000000000000000000000000 : ℝ)*base76 + (246058865602631627/94437500000000000000000000000000 : ℝ)*base78 + (85996224424381627/94437500000000000000000000000000 : ℝ)*base80 + (834322312843/1888750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (456579/312500000000000000000 : ℝ)*base89 + (456579/312500000000000000000 : ℝ)*base91 + (456579/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-4303/5000 : ℝ) ≤ (-81270095344615657218129302633493/94437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (624047/50000000000000 : ℝ)*(upper1) + (3387447/100000000000000 : ℝ)*(upper3) + (119511/50000000000000 : ℝ)*(lower4) + (2545609051655793/100000000000000 : ℝ)*(major0) + (2545609051655793/100000000000000 : ℝ)*(major1) + (2545609051655793/100000000000000 : ℝ)*(major2) + (64061563/10000000000000 : ℝ)*(sp4) + (2474181609/25000000000000 : ℝ)*(sp5) + (2961456667/100000000000000 : ℝ)*(sp6) + (408521613/25000000000000 : ℝ)*(sp7) + (1784317889848967/50000000000000 : ℝ)*(sp12) + (446078315448391/12500000000000 : ℝ)*(sp13) + (55759897794639/1562500000000 : ℝ)*(sp14) + (1551265721214973/100000000000000 : ℝ)*(sp15) + (775633677650713/50000000000000 : ℝ)*(f.failure) + (3568636420313563/100000000000000 : ℝ)*(f.sum) + (22405236029777/3777500000000000000000000000 : ℝ)*base65 + (16413334206665331/377750000000000000000000000000000 : ℝ)*base67 + (21265586759579415331/377750000000000000000000000000000 : ℝ)*base69 + (3180520746519415331/377750000000000000000000000000000 : ℝ)*base71 + (3984992618229/7555000000000000000000000000 : ℝ)*base73 + (1777547188542584669/377750000000000000000000000000000 : ℝ)*base76 + (4254514229336665331/377750000000000000000000000000000 : ℝ)*base77 + (1193541769769415331/377750000000000000000000000000000 : ℝ)*base79 + (2622821607551/1888750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (44899571/5000000000000000000000 : ℝ)*base89 + (44899571/5000000000000000000000 : ℝ)*base91 + (44899571/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1521_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63751/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5867/10000 : ℝ) else (16083/20000 : ℝ) ≤ X j i ∧ X j i ≤ (4303/5000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1521_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1521_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63751/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5867/10000 : ℝ) else (16083/20000 : ℝ) ≤ X j i ∧ X j i ≤ (4303/5000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1521_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1521_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4537/1024 : ℝ) ≤ p) (hpb : p ≤ (4539/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164098667/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (219/2000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63751/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5867/10000 : ℝ) else (16083/20000 : ℝ) ≤ X j i ∧ X j i ≤ (4303/5000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1521_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
