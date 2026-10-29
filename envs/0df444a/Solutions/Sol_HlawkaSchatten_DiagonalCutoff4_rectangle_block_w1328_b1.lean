-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1328_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:55:34.52503+00:00
-- url     : https://prove2.me/submissions/c5aaa2b8-5885-4cda-9564-30f139ea245a

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
theorem support_rectangle_w1328_s3_0 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-128388727/625000000 : ℝ)*x 0 + (1357248031/2500000000 : ℝ)*x 1 + (5229857747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128388727/625000000 : ℝ)^67 ≤ (12502782594123/100000000000000 : ℝ)^51 := by
    have hnat : (128388727 : ℕ)^67*100000000000000^51 ≤ 12502782594123^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128388727 625000000 12502782594123 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357248031/2500000000 : ℝ)^67 ≤ (8964454389439/20000000000000 : ℝ)^51 := by
    have hnat : (1357248031 : ℕ)^67*20000000000000^51 ≤ 8964454389439^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357248031 2500000000 8964454389439 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229857747/10000000000 : ℝ)^67 ≤ (42674945440367/100000000000000 : ℝ)^51 := by
    have hnat : (5229857747 : ℕ)^67*100000000000000^51 ≤ 42674945440367^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229857747 10000000000 42674945440367 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128388727/625000000 : ℝ), (1357248031/2500000000 : ℝ), (5229857747/10000000000 : ℝ)] ![(12502782594123/100000000000000 : ℝ), (8964454389439/20000000000000 : ℝ), (42674945440367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128388727/625000000 : ℝ)|^67 ≤ (12502782594123/100000000000000 : ℝ)^51
        have hw : |(-128388727/625000000 : ℝ)|=(128388727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357248031/2500000000 : ℝ)|^67 ≤ (8964454389439/20000000000000 : ℝ)^51
        have hw : |(1357248031/2500000000 : ℝ)|=(1357248031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229857747/10000000000 : ℝ)|^67 ≤ (42674945440367/100000000000000 : ℝ)^51
        have hw : |(5229857747/10000000000 : ℝ)|=(5229857747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_1 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1338298671/2500000000 : ℝ)*x 0 + (-539007359/2500000000 : ℝ)*x 1 + (130746437/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338298671/2500000000 : ℝ)^67 ≤ (44001960854087/100000000000000 : ℝ)^51 := by
    have hnat : (1338298671 : ℕ)^67*100000000000000^51 ≤ 44001960854087^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338298671 2500000000 44001960854087 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539007359/2500000000 : ℝ)^67 ≤ (13323096564383/100000000000000 : ℝ)^51 := by
    have hnat : (539007359 : ℕ)^67*100000000000000^51 ≤ 13323096564383^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539007359 2500000000 13323096564383 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130746437/250000000 : ℝ)^67 ≤ (21337471289087/50000000000000 : ℝ)^51 := by
    have hnat : (130746437 : ℕ)^67*50000000000000^51 ≤ 21337471289087^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130746437 250000000 21337471289087 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338298671/2500000000 : ℝ), (-539007359/2500000000 : ℝ), (130746437/250000000 : ℝ)] ![(44001960854087/100000000000000 : ℝ), (13323096564383/100000000000000 : ℝ), (21337471289087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338298671/2500000000 : ℝ)|^67 ≤ (44001960854087/100000000000000 : ℝ)^51
        have hw : |(1338298671/2500000000 : ℝ)|=(1338298671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-539007359/2500000000 : ℝ)|^67 ≤ (13323096564383/100000000000000 : ℝ)^51
        have hw : |(-539007359/2500000000 : ℝ)|=(539007359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130746437/250000000 : ℝ)|^67 ≤ (21337471289087/50000000000000 : ℝ)^51
        have hw : |(130746437/250000000 : ℝ)|=(130746437/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_2 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1338298741/2500000000 : ℝ)*x 0 + (2614928541/5000000000 : ℝ)*x 1 + (-539007397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338298741/2500000000 : ℝ)^67 ≤ (11000490969417/25000000000000 : ℝ)^51 := by
    have hnat : (1338298741 : ℕ)^67*25000000000000^51 ≤ 11000490969417^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338298741 2500000000 11000490969417 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614928541/5000000000 : ℝ)^67 ≤ (42674938311683/100000000000000 : ℝ)^51 := by
    have hnat : (2614928541 : ℕ)^67*100000000000000^51 ≤ 42674938311683^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614928541 5000000000 42674938311683 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539007397/2500000000 : ℝ)^67 ≤ (13323097798337/100000000000000 : ℝ)^51 := by
    have hnat : (539007397 : ℕ)^67*100000000000000^51 ≤ 13323097798337^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539007397 2500000000 13323097798337 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338298741/2500000000 : ℝ), (2614928541/5000000000 : ℝ), (-539007397/2500000000 : ℝ)] ![(11000490969417/25000000000000 : ℝ), (42674938311683/100000000000000 : ℝ), (13323097798337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338298741/2500000000 : ℝ)|^67 ≤ (11000490969417/25000000000000 : ℝ)^51
        have hw : |(1338298741/2500000000 : ℝ)|=(1338298741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614928541/5000000000 : ℝ)|^67 ≤ (42674938311683/100000000000000 : ℝ)^51
        have hw : |(2614928541/5000000000 : ℝ)|=(2614928541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-539007397/2500000000 : ℝ)|^67 ≤ (13323097798337/100000000000000 : ℝ)^51
        have hw : |(-539007397/2500000000 : ℝ)|=(539007397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_3 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1082285183/2500000000 : ℝ)*x 0 + (4126359299/10000000000 : ℝ)*x 1 + (4541264903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082285183/2500000000 : ℝ)^67 ≤ (6658273739063/20000000000000 : ℝ)^51 := by
    have hnat : (1082285183 : ℕ)^67*20000000000000^51 ≤ 6658273739063^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082285183 2500000000 6658273739063 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126359299/10000000000 : ℝ)^67 ≤ (31257959389269/100000000000000 : ℝ)^51 := by
    have hnat : (4126359299 : ℕ)^67*100000000000000^51 ≤ 31257959389269^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126359299 10000000000 31257959389269 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4541264903/10000000000 : ℝ)^67 ≤ (35450671909833/100000000000000 : ℝ)^51 := by
    have hnat : (4541264903 : ℕ)^67*100000000000000^51 ≤ 35450671909833^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541264903 10000000000 35450671909833 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082285183/2500000000 : ℝ), (4126359299/10000000000 : ℝ), (4541264903/10000000000 : ℝ)] ![(6658273739063/20000000000000 : ℝ), (31257959389269/100000000000000 : ℝ), (35450671909833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082285183/2500000000 : ℝ)|^67 ≤ (6658273739063/20000000000000 : ℝ)^51
        have hw : |(1082285183/2500000000 : ℝ)|=(1082285183/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4126359299/10000000000 : ℝ)|^67 ≤ (31257959389269/100000000000000 : ℝ)^51
        have hw : |(4126359299/10000000000 : ℝ)|=(4126359299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4541264903/10000000000 : ℝ)|^67 ≤ (35450671909833/100000000000000 : ℝ)^51
        have hw : |(4541264903/10000000000 : ℝ)|=(4541264903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_4 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027119981/5000000000 : ℝ)*x 0 + (2615347189/5000000000 : ℝ)*x 1 + (1085630043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027119981/5000000000 : ℝ)^67 ≤ (1562868143741/12500000000000 : ℝ)^51 := by
    have hnat : (1027119981 : ℕ)^67*12500000000000^51 ≤ 1562868143741^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027119981 5000000000 1562868143741 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615347189/5000000000 : ℝ)^67 ≤ (42683914203929/100000000000000 : ℝ)^51 := by
    have hnat : (2615347189 : ℕ)^67*100000000000000^51 ≤ 42683914203929^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615347189 5000000000 42683914203929 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085630043/2000000000 : ℝ)^67 ≤ (22406570310383/50000000000000 : ℝ)^51 := by
    have hnat : (1085630043 : ℕ)^67*50000000000000^51 ≤ 22406570310383^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085630043 2000000000 22406570310383 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027119981/5000000000 : ℝ), (2615347189/5000000000 : ℝ), (1085630043/2000000000 : ℝ)] ![(1562868143741/12500000000000 : ℝ), (42683914203929/100000000000000 : ℝ), (22406570310383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027119981/5000000000 : ℝ)|^67 ≤ (1562868143741/12500000000000 : ℝ)^51
        have hw : |(-1027119981/5000000000 : ℝ)|=(1027119981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615347189/5000000000 : ℝ)|^67 ≤ (42683914203929/100000000000000 : ℝ)^51
        have hw : |(2615347189/5000000000 : ℝ)|=(2615347189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085630043/2000000000 : ℝ)|^67 ≤ (22406570310383/50000000000000 : ℝ)^51
        have hw : |(1085630043/2000000000 : ℝ)|=(1085630043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_5 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (212079343/400000000 : ℝ)*x 0 + (-489434241/2500000000 : ℝ)*x 1 + (1357037603/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212079343/400000000 : ℝ)^67 ≤ (43449789128119/100000000000000 : ℝ)^51 := by
    have hnat : (212079343 : ℕ)^67*100000000000000^51 ≤ 43449789128119^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212079343 400000000 43449789128119 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489434241/2500000000 : ℝ)^67 ≤ (11737068093959/100000000000000 : ℝ)^51 := by
    have hnat : (489434241 : ℕ)^67*100000000000000^51 ≤ 11737068093959^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489434241 2500000000 11737068093959 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357037603/2500000000 : ℝ)^67 ≤ (44813142757371/100000000000000 : ℝ)^51 := by
    have hnat : (1357037603 : ℕ)^67*100000000000000^51 ≤ 44813142757371^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357037603 2500000000 44813142757371 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212079343/400000000 : ℝ), (-489434241/2500000000 : ℝ), (1357037603/2500000000 : ℝ)] ![(43449789128119/100000000000000 : ℝ), (11737068093959/100000000000000 : ℝ), (44813142757371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212079343/400000000 : ℝ)|^67 ≤ (43449789128119/100000000000000 : ℝ)^51
        have hw : |(212079343/400000000 : ℝ)|=(212079343/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489434241/2500000000 : ℝ)|^67 ≤ (11737068093959/100000000000000 : ℝ)^51
        have hw : |(-489434241/2500000000 : ℝ)|=(489434241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357037603/2500000000 : ℝ)|^67 ≤ (44813142757371/100000000000000 : ℝ)^51
        have hw : |(1357037603/2500000000 : ℝ)|=(1357037603/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_6 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5301985261/10000000000 : ℝ)*x 0 + (5428149231/10000000000 : ℝ)*x 1 + (-978868143/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301985261/10000000000 : ℝ)^67 ≤ (5431225909947/12500000000000 : ℝ)^51 := by
    have hnat : (5301985261 : ℕ)^67*12500000000000^51 ≤ 5431225909947^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301985261 10000000000 5431225909947 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428149231/10000000000 : ℝ)^67 ≤ (44813129948583/100000000000000 : ℝ)^51 := by
    have hnat : (5428149231 : ℕ)^67*100000000000000^51 ≤ 44813129948583^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428149231 10000000000 44813129948583 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978868143/5000000000 : ℝ)^67 ≤ (586853137699/5000000000000 : ℝ)^51 := by
    have hnat : (978868143 : ℕ)^67*5000000000000^51 ≤ 586853137699^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978868143 5000000000 586853137699 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301985261/10000000000 : ℝ), (5428149231/10000000000 : ℝ), (-978868143/5000000000 : ℝ)] ![(5431225909947/12500000000000 : ℝ), (44813129948583/100000000000000 : ℝ), (586853137699/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301985261/10000000000 : ℝ)|^67 ≤ (5431225909947/12500000000000 : ℝ)^51
        have hw : |(5301985261/10000000000 : ℝ)|=(5301985261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428149231/10000000000 : ℝ)|^67 ≤ (44813129948583/100000000000000 : ℝ)^51
        have hw : |(5428149231/10000000000 : ℝ)|=(5428149231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-978868143/5000000000 : ℝ)|^67 ≤ (586853137699/5000000000000 : ℝ)^51
        have hw : |(-978868143/5000000000 : ℝ)|=(978868143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_7 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (173167311/400000000 : ℝ)*x 0 + (4539521661/10000000000 : ℝ)*x 1 + (4128112829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173167311/400000000 : ℝ)^67 ≤ (16645896720479/50000000000000 : ℝ)^51 := by
    have hnat : (173167311 : ℕ)^67*50000000000000^51 ≤ 16645896720479^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173167311 400000000 16645896720479 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539521661/10000000000 : ℝ)^67 ≤ (885819883913/2500000000000 : ℝ)^51 := by
    have hnat : (4539521661 : ℕ)^67*2500000000000^51 ≤ 885819883913^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539521661 10000000000 885819883913 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128112829/10000000000 : ℝ)^67 ≤ (15637705597197/50000000000000 : ℝ)^51 := by
    have hnat : (4128112829 : ℕ)^67*50000000000000^51 ≤ 15637705597197^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128112829 10000000000 15637705597197 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173167311/400000000 : ℝ), (4539521661/10000000000 : ℝ), (4128112829/10000000000 : ℝ)] ![(16645896720479/50000000000000 : ℝ), (885819883913/2500000000000 : ℝ), (15637705597197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173167311/400000000 : ℝ)|^67 ≤ (16645896720479/50000000000000 : ℝ)^51
        have hw : |(173167311/400000000 : ℝ)|=(173167311/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539521661/10000000000 : ℝ)|^67 ≤ (885819883913/2500000000000 : ℝ)^51
        have hw : |(4539521661/10000000000 : ℝ)|=(4539521661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128112829/10000000000 : ℝ)|^67 ≤ (15637705597197/50000000000000 : ℝ)^51
        have hw : |(4128112829/10000000000 : ℝ)|=(4128112829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_8 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-42439959/5000000000 : ℝ)*x 0 + (2861594677/5000000000 : ℝ)*x 1 + (6058390403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42439959/5000000000 : ℝ)^67 ≤ (95057912699/50000000000000 : ℝ)^51 := by
    have hnat : (42439959 : ℕ)^67*50000000000000^51 ≤ 95057912699^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42439959 5000000000 95057912699 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2861594677/5000000000 : ℝ)^67 ≤ (24020000831263/50000000000000 : ℝ)^51 := by
    have hnat : (2861594677 : ℕ)^67*50000000000000^51 ≤ 24020000831263^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2861594677 5000000000 24020000831263 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6058390403/10000000000 : ℝ)^67 ≤ (51769882497873/100000000000000 : ℝ)^51 := by
    have hnat : (6058390403 : ℕ)^67*100000000000000^51 ≤ 51769882497873^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6058390403 10000000000 51769882497873 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42439959/5000000000 : ℝ), (2861594677/5000000000 : ℝ), (6058390403/10000000000 : ℝ)] ![(95057912699/50000000000000 : ℝ), (24020000831263/50000000000000 : ℝ), (51769882497873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42439959/5000000000 : ℝ)|^67 ≤ (95057912699/50000000000000 : ℝ)^51
        have hw : |(-42439959/5000000000 : ℝ)|=(42439959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2861594677/5000000000 : ℝ)|^67 ≤ (24020000831263/50000000000000 : ℝ)^51
        have hw : |(2861594677/5000000000 : ℝ)|=(2861594677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6058390403/10000000000 : ℝ)|^67 ≤ (51769882497873/100000000000000 : ℝ)^51
        have hw : |(6058390403/10000000000 : ℝ)|=(6058390403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_9 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (125771051/1250000000 : ℝ)*x 0 + (-4294006377/10000000000 : ℝ)*x 1 + (6964071407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (125771051/1250000000 : ℝ)^67 ≤ (1223835523513/25000000000000 : ℝ)^51 := by
    have hnat : (125771051 : ℕ)^67*25000000000000^51 ≤ 1223835523513^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125771051 1250000000 1223835523513 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4294006377/10000000000 : ℝ)^67 ≤ (16468435959537/50000000000000 : ℝ)^51 := by
    have hnat : (4294006377 : ℕ)^67*50000000000000^51 ≤ 16468435959537^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4294006377 10000000000 16468435959537 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6964071407/10000000000 : ℝ)^67 ≤ (62167785978931/100000000000000 : ℝ)^51 := by
    have hnat : (6964071407 : ℕ)^67*100000000000000^51 ≤ 62167785978931^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6964071407 10000000000 62167785978931 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(125771051/1250000000 : ℝ), (-4294006377/10000000000 : ℝ), (6964071407/10000000000 : ℝ)] ![(1223835523513/25000000000000 : ℝ), (16468435959537/50000000000000 : ℝ), (62167785978931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(125771051/1250000000 : ℝ)|^67 ≤ (1223835523513/25000000000000 : ℝ)^51
        have hw : |(125771051/1250000000 : ℝ)|=(125771051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4294006377/10000000000 : ℝ)|^67 ≤ (16468435959537/50000000000000 : ℝ)^51
        have hw : |(-4294006377/10000000000 : ℝ)|=(4294006377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6964071407/10000000000 : ℝ)|^67 ≤ (62167785978931/100000000000000 : ℝ)^51
        have hw : |(6964071407/10000000000 : ℝ)|=(6964071407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_10 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1006182859/10000000000 : ℝ)*x 0 + (1741025767/2500000000 : ℝ)*x 1 + (-2146980181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006182859/10000000000 : ℝ)^67 ≤ (4895434460847/100000000000000 : ℝ)^51 := by
    have hnat : (1006182859 : ℕ)^67*100000000000000^51 ≤ 4895434460847^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006182859 10000000000 4895434460847 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1741025767/2500000000 : ℝ)^67 ≤ (12433631456949/20000000000000 : ℝ)^51 := by
    have hnat : (1741025767 : ℕ)^67*20000000000000^51 ≤ 12433631456949^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741025767 2500000000 12433631456949 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2146980181/5000000000 : ℝ)^67 ≤ (4117051029267/12500000000000 : ℝ)^51 := by
    have hnat : (2146980181 : ℕ)^67*12500000000000^51 ≤ 4117051029267^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146980181 5000000000 4117051029267 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1006182859/10000000000 : ℝ), (1741025767/2500000000 : ℝ), (-2146980181/5000000000 : ℝ)] ![(4895434460847/100000000000000 : ℝ), (12433631456949/20000000000000 : ℝ), (4117051029267/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1006182859/10000000000 : ℝ)|^67 ≤ (4895434460847/100000000000000 : ℝ)^51
        have hw : |(1006182859/10000000000 : ℝ)|=(1006182859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1741025767/2500000000 : ℝ)|^67 ≤ (12433631456949/20000000000000 : ℝ)^51
        have hw : |(1741025767/2500000000 : ℝ)|=(1741025767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2146980181/5000000000 : ℝ)|^67 ≤ (4117051029267/12500000000000 : ℝ)^51
        have hw : |(-2146980181/5000000000 : ℝ)|=(2146980181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s3_11 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (925770527/10000000000 : ℝ)*x 0 + (586346141/1000000000 : ℝ)*x 1 + (2769500777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (925770527/10000000000 : ℝ)^67 ≤ (548503142867/12500000000000 : ℝ)^51 := by
    have hnat : (925770527 : ℕ)^67*12500000000000^51 ≤ 548503142867^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      925770527 10000000000 548503142867 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (586346141/1000000000 : ℝ)^67 ≤ (12398184709497/25000000000000 : ℝ)^51 := by
    have hnat : (586346141 : ℕ)^67*25000000000000^51 ≤ 12398184709497^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      586346141 1000000000 12398184709497 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2769500777/5000000000 : ℝ)^67 ≤ (5752404501791/12500000000000 : ℝ)^51 := by
    have hnat : (2769500777 : ℕ)^67*12500000000000^51 ≤ 5752404501791^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2769500777 5000000000 5752404501791 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(925770527/10000000000 : ℝ), (586346141/1000000000 : ℝ), (2769500777/5000000000 : ℝ)] ![(548503142867/12500000000000 : ℝ), (12398184709497/25000000000000 : ℝ), (5752404501791/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(925770527/10000000000 : ℝ)|^67 ≤ (548503142867/12500000000000 : ℝ)^51
        have hw : |(925770527/10000000000 : ℝ)|=(925770527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(586346141/1000000000 : ℝ)|^67 ≤ (12398184709497/25000000000000 : ℝ)^51
        have hw : |(586346141/1000000000 : ℝ)|=(586346141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2769500777/5000000000 : ℝ)|^67 ≤ (5752404501791/12500000000000 : ℝ)^51
        have hw : |(2769500777/5000000000 : ℝ)|=(2769500777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1328_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (101/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1081/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (101/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9759/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (101/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9759/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (101/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9759/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (101/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9759/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (101/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9759/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (101/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9759/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9759/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (5876539748026571/100000000000000000000 : ℝ) := by
    have hpowers : (9759/100000 : ℝ)^4287 ≤ (5876539748026571/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9759 : ℕ)^4287*100000000000000000000^1024 ≤ 5876539748026571^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9759 100000 5876539748026571 100000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9759/100000 : ℝ)) (X := (5876539748026571/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (101/625 : ℝ) ^ (4287/1024 : ℝ) ≤ (48542393512486359/100000000000000000000 : ℝ) := by
    have hpowers : (101/625 : ℝ)^4287 ≤ (48542393512486359/100000000000000000000 : ℝ)^1024 := by
      have hnat : (101 : ℕ)^4287*100000000000000000000^1024 ≤ 48542393512486359^1024*625^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101 625 48542393512486359 100000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (101/625 : ℝ)) (X := (48542393512486359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005876539748026571/50000000000000000000 : ℝ) ≤ (10000280723469223/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50005876539748026571/50000000000000000000 : ℝ)^1024 ≤ (10000280723469223/10000000000000000 : ℝ)^4287 := by
      have hnat : (50005876539748026571 : ℕ)^1024*10000000000000000^4287 ≤ 10000280723469223^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005876539748026571 50000000000000000000 10000280723469223 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280723469223/10000000000000000 : ℝ)) (X := (50005876539748026571/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10005441893326051293/10000000000000000000 : ℝ) ≤ (625081224414809/625000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (10005441893326051293/10000000000000000000 : ℝ)^1024 ≤ (625081224414809/625000000000000 : ℝ)^4287 := by
      have hnat : (10005441893326051293 : ℕ)^1024*625000000000000^4287 ≤ 625081224414809^4287*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005441893326051293 10000000000000000000 625081224414809 625000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625081224414809/625000000000000 : ℝ)) (X := (10005441893326051293/10000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048542393512486359/50000000000000000000 : ℝ) ≤ (2000463691560933/2000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50048542393512486359/50000000000000000000 : ℝ)^1024 ≤ (2000463691560933/2000000000000000 : ℝ)^4287 := by
      have hnat : (50048542393512486359 : ℕ)^1024*2000000000000000^4287 ≤ 2000463691560933^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048542393512486359 50000000000000000000 2000463691560933 2000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000463691560933/2000000000000000 : ℝ)) (X := (50048542393512486359/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5876539748026571/100000000000000000000 : ℝ) ≤ ((12798382132309383589/12802000000000000000 : ℝ)+2*(1018867167721/640100000000000 : ℝ)*(9759/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (12798382132309383589/12802000000000000000 : ℝ)+2*(1018867167721/640100000000000 : ℝ)*(9759/100000 : ℝ)=(10000280723469223/10000000000000000 : ℝ) by norm_num, show 1+2*(5876539748026571/100000000000000000000 : ℝ)=(50005876539748026571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48542393512486359/100000000000000000000 : ℝ)+(5876539748026571/100000000000000000000 : ℝ) ≤ ((12798382132309383589/12802000000000000000 : ℝ)+(1018867167721/640100000000000 : ℝ)*((101/625 : ℝ)+(9759/100000 : ℝ)))^(4287/1024 : ℝ) := by
    rw [show (12798382132309383589/12802000000000000000 : ℝ)+(1018867167721/640100000000000 : ℝ)*((101/625 : ℝ)+(9759/100000 : ℝ))=(625081224414809/625000000000000 : ℝ) by norm_num, show 1+(48542393512486359/100000000000000000000 : ℝ)+(5876539748026571/100000000000000000000 : ℝ)=(10005441893326051293/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48542393512486359/100000000000000000000 : ℝ) ≤ ((12798382132309383589/12802000000000000000 : ℝ)+2*(1018867167721/640100000000000 : ℝ)*(101/625 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (12798382132309383589/12802000000000000000 : ℝ)+2*(1018867167721/640100000000000 : ℝ)*(101/625 : ℝ)=(2000463691560933/2000000000000000 : ℝ) by norm_num, show 1+2*(48542393512486359/100000000000000000000 : ℝ)=(50048542393512486359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12798382132309383589/12802000000000000000 : ℝ)*(X 1 0+X 2 0)+(1018867167721/640100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (9759/100000 : ℝ)) (hi := (101/625 : ℝ)) (c := (12798382132309383589/12802000000000000000 : ℝ)) (alpha := (1018867167721/640100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12798382132309383589/12802000000000000000 : ℝ)*(X 0 1+X 2 1)+(1018867167721/640100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (9759/100000 : ℝ)) (hi := (101/625 : ℝ)) (c := (12798382132309383589/12802000000000000000 : ℝ)) (alpha := (1018867167721/640100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12798382132309383589/12802000000000000000 : ℝ)*(X 0 2+X 1 2)+(1018867167721/640100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (9759/100000 : ℝ)) (hi := (101/625 : ℝ)) (c := (12798382132309383589/12802000000000000000 : ℝ)) (alpha := (1018867167721/640100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-128388727/625000000 : ℝ)*X 0 0+(1357248031/2500000000 : ℝ)*X 0 1+(5229857747/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338298671/2500000000 : ℝ)*X 1 0+(-539007359/2500000000 : ℝ)*X 1 1+(130746437/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338298741/2500000000 : ℝ)*X 2 0+(2614928541/5000000000 : ℝ)*X 2 1+(-539007397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1082285183/2500000000 : ℝ)*X 0 0+(4126359299/10000000000 : ℝ)*X 0 1+(4541264903/10000000000 : ℝ)*X 0 2+(1082285183/2500000000 : ℝ)*X 1 0+(4126359299/10000000000 : ℝ)*X 1 1+(4541264903/10000000000 : ℝ)*X 1 2+(1082285183/2500000000 : ℝ)*X 2 0+(4126359299/10000000000 : ℝ)*X 2 1+(4541264903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1027119981/5000000000 : ℝ)*X 0 0+(2615347189/5000000000 : ℝ)*X 0 1+(1085630043/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212079343/400000000 : ℝ)*X 1 0+(-489434241/2500000000 : ℝ)*X 1 1+(1357037603/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301985261/10000000000 : ℝ)*X 2 0+(5428149231/10000000000 : ℝ)*X 2 1+(-978868143/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((173167311/400000000 : ℝ)*X 0 0+(4539521661/10000000000 : ℝ)*X 0 1+(4128112829/10000000000 : ℝ)*X 0 2+(173167311/400000000 : ℝ)*X 1 0+(4539521661/10000000000 : ℝ)*X 1 1+(4128112829/10000000000 : ℝ)*X 1 2+(173167311/400000000 : ℝ)*X 2 0+(4539521661/10000000000 : ℝ)*X 2 1+(4128112829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-42439959/5000000000 : ℝ)*X 0 0+(2861594677/5000000000 : ℝ)*X 0 1+(6058390403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((125771051/1250000000 : ℝ)*X 1 0+(-4294006377/10000000000 : ℝ)*X 1 1+(6964071407/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1006182859/10000000000 : ℝ)*X 2 0+(1741025767/2500000000 : ℝ)*X 2 1+(-2146980181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((925770527/10000000000 : ℝ)*X 0 0+(586346141/1000000000 : ℝ)*X 0 1+(2769500777/5000000000 : ℝ)*X 0 2+(925770527/10000000000 : ℝ)*X 1 0+(586346141/1000000000 : ℝ)*X 1 1+(2769500777/5000000000 : ℝ)*X 1 2+(925770527/10000000000 : ℝ)*X 2 0+(586346141/1000000000 : ℝ)*X 2 1+(2769500777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (540770402715119234551399239/80012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (34400819/6250000000000 : ℝ)*(lower2) + (464494382220461/12500000000000 : ℝ)*(major0) + (464494382220461/12500000000000 : ℝ)*(major1) + (464494382220461/12500000000000 : ℝ)*(major2) + (2510861944431641/50000000000000 : ℝ)*(sp0) + (1255429613643253/25000000000000 : ℝ)*(sp1) + (5021714856430773/100000000000000 : ℝ)*(sp2) + (602545656293913/25000000000000 : ℝ)*(sp3) + (3224580473/50000000000000 : ℝ)*(sp5) + (1104415639/10000000000000 : ℝ)*(sp6) + (1313865179/100000000000000 : ℝ)*(sp7) + (2011723881/100000000000000 : ℝ)*(sp8) + (199370641/20000000000000 : ℝ)*(sp9) + (25306787/50000000000000 : ℝ)*(sp11) + (1205091994827203/50000000000000 : ℝ)*(f.failure) + (5021725900587163/100000000000000 : ℝ)*(f.sum) + (133660927312523/32005000000000000000000000000 : ℝ)*base65 + (809165476374809529/160025000000000000000000000000000 : ℝ)*base67 + (1131405675980034529/160025000000000000000000000000000 : ℝ)*base69 + (1287080645193909529/160025000000000000000000000000000 : ℝ)*base71 + (26982970658841/16002500000000000000000000000 : ℝ)*base74 + (1373445208748784529/160025000000000000000000000000000 : ℝ)*base75 + (781254876024809529/160025000000000000000000000000000 : ℝ)*base77 + (1029765278268959529/160025000000000000000000000000000 : ℝ)*base79 + (18811839203347/32005000000000000000000000000 : ℝ)*base82 + (14037727/1250000000000000000000 : ℝ)*base89 + (14037727/1250000000000000000000 : ℝ)*base91 + (14037727/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (897906211618886038685228493/320050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40725427/25000000000000 : ℝ)*(lower2) + (1873784617844593/50000000000000 : ℝ)*(major0) + (1873784617844593/50000000000000 : ℝ)*(major1) + (1873784617844593/50000000000000 : ℝ)*(major2) + (8548245961/100000000000000 : ℝ)*(sp0) + (1810104273/20000000000000 : ℝ)*(sp1) + (3136864537/50000000000000 : ℝ)*(sp3) + (1012887865390307/20000000000000 : ℝ)*(sp4) + (506444024968029/10000000000000 : ℝ)*(sp5) + (5064447799630493/100000000000000 : ℝ)*(sp6) + (607670563989273/25000000000000 : ℝ)*(sp7) + (1425004159/100000000000000 : ℝ)*(sp8) + (750285581/50000000000000 : ℝ)*(sp10) + (273986627/50000000000000 : ℝ)*(sp11) + (121534453882971/5000000000000 : ℝ)*(f.failure) + (1012889860040331/20000000000000 : ℝ)*(f.sum) + (20239123607651/8001250000000000000000000000 : ℝ)*base66 + (8989039292018155723/640100000000000000000000000000000 : ℝ)*base68 + (12598002475299855723/640100000000000000000000000000000 : ℝ)*base70 + (10070754509535955723/640100000000000000000000000000000 : ℝ)*base72 + (3589849839723/4000625000000000000000000000 : ℝ)*base74 + (8855986651710955723/640100000000000000000000000000000 : ℝ)*base76 + (11298860240518055723/640100000000000000000000000000000 : ℝ)*base78 + (14889046604300055723/640100000000000000000000000000000 : ℝ)*base80 + (3091442333143/16002500000000000000000000000 : ℝ)*base81 + (1562039/125000000000000000000 : ℝ)*base89 + (1562039/125000000000000000000 : ℝ)*base91 + (1562039/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1328_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (101/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1328_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1328_s4_0 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055796781/10000000000 : ℝ)*x 0 + (1083250317/2000000000 : ℝ)*x 1 + (104831263/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055796781/10000000000 : ℝ)^67 ≤ (12515394753397/100000000000000 : ℝ)^51 := by
    have hnat : (2055796781 : ℕ)^67*100000000000000^51 ≤ 12515394753397^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055796781 10000000000 12515394753397 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1083250317/2000000000 : ℝ)^67 ≤ (44684135877427/100000000000000 : ℝ)^51 := by
    have hnat : (1083250317 : ℕ)^67*100000000000000^51 ≤ 44684135877427^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083250317 2000000000 44684135877427 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104831263/200000000 : ℝ)^67 ≤ (42800469352553/100000000000000 : ℝ)^51 := by
    have hnat : (104831263 : ℕ)^67*100000000000000^51 ≤ 42800469352553^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104831263 200000000 42800469352553 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055796781/10000000000 : ℝ), (1083250317/2000000000 : ℝ), (104831263/200000000 : ℝ)] ![(12515394753397/100000000000000 : ℝ), (44684135877427/100000000000000 : ℝ), (42800469352553/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055796781/10000000000 : ℝ)|^67 ≤ (12515394753397/100000000000000 : ℝ)^51
        have hw : |(-2055796781/10000000000 : ℝ)|=(2055796781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1083250317/2000000000 : ℝ)|^67 ≤ (44684135877427/100000000000000 : ℝ)^51
        have hw : |(1083250317/2000000000 : ℝ)|=(1083250317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104831263/200000000 : ℝ)|^67 ≤ (42800469352553/100000000000000 : ℝ)^51
        have hw : |(104831263/200000000 : ℝ)|=(104831263/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s4_1 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5349954917/10000000000 : ℝ)*x 0 + (-1072433503/5000000000 : ℝ)*x 1 + (5241563031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349954917/10000000000 : ℝ)^67 ≤ (10991744884203/25000000000000 : ℝ)^51 := by
    have hnat : (5349954917 : ℕ)^67*25000000000000^51 ≤ 10991744884203^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349954917 10000000000 10991744884203 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072433503/5000000000 : ℝ)^67 ≤ (2646510474363/20000000000000 : ℝ)^51 := by
    have hnat : (1072433503 : ℕ)^67*20000000000000^51 ≤ 2646510474363^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072433503 5000000000 2646510474363 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241563031/10000000000 : ℝ)^67 ≤ (42800468075999/100000000000000 : ℝ)^51 := by
    have hnat : (5241563031 : ℕ)^67*100000000000000^51 ≤ 42800468075999^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241563031 10000000000 42800468075999 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349954917/10000000000 : ℝ), (-1072433503/5000000000 : ℝ), (5241563031/10000000000 : ℝ)] ![(10991744884203/25000000000000 : ℝ), (2646510474363/20000000000000 : ℝ), (42800468075999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349954917/10000000000 : ℝ)|^67 ≤ (10991744884203/25000000000000 : ℝ)^51
        have hw : |(5349954917/10000000000 : ℝ)|=(5349954917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072433503/5000000000 : ℝ)|^67 ≤ (2646510474363/20000000000000 : ℝ)^51
        have hw : |(-1072433503/5000000000 : ℝ)|=(1072433503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241563031/10000000000 : ℝ)|^67 ≤ (42800468075999/100000000000000 : ℝ)^51
        have hw : |(5241563031/10000000000 : ℝ)|=(5241563031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s4_2 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5349954983/10000000000 : ℝ)*x 0 + (131039069/250000000 : ℝ)*x 1 + (-2144867277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349954983/10000000000 : ℝ)^67 ≤ (21983490124689/50000000000000 : ℝ)^51 := by
    have hnat : (5349954983 : ℕ)^67*50000000000000^51 ≤ 21983490124689^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349954983 10000000000 21983490124689 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131039069/250000000 : ℝ)^67 ≤ (5350058146111/12500000000000 : ℝ)^51 := by
    have hnat : (131039069 : ℕ)^67*12500000000000^51 ≤ 5350058146111^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131039069 250000000 5350058146111 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2144867277/10000000000 : ℝ)^67 ≤ (3308138642061/25000000000000 : ℝ)^51 := by
    have hnat : (2144867277 : ℕ)^67*25000000000000^51 ≤ 3308138642061^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2144867277 10000000000 3308138642061 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349954983/10000000000 : ℝ), (131039069/250000000 : ℝ), (-2144867277/10000000000 : ℝ)] ![(21983490124689/50000000000000 : ℝ), (5350058146111/12500000000000 : ℝ), (3308138642061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349954983/10000000000 : ℝ)|^67 ≤ (21983490124689/50000000000000 : ℝ)^51
        have hw : |(5349954983/10000000000 : ℝ)|=(5349954983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131039069/250000000 : ℝ)|^67 ≤ (5350058146111/12500000000000 : ℝ)^51
        have hw : |(131039069/250000000 : ℝ)|=(131039069/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2144867277/10000000000 : ℝ)|^67 ≤ (3308138642061/25000000000000 : ℝ)^51
        have hw : |(-2144867277/10000000000 : ℝ)|=(2144867277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s4_3 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (866019403/2000000000 : ℝ)*x 0 + (16606829/40000000 : ℝ)*x 1 + (4515679143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866019403/2000000000 : ℝ)^67 ≤ (6660206001233/20000000000000 : ℝ)^51 := by
    have hnat : (866019403 : ℕ)^67*20000000000000^51 ≤ 6660206001233^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866019403 2000000000 6660206001233 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16606829/40000000 : ℝ)^67 ≤ (31510457867243/100000000000000 : ℝ)^51 := by
    have hnat : (16606829 : ℕ)^67*100000000000000^51 ≤ 31510457867243^51*40000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16606829 40000000 31510457867243 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4515679143/10000000000 : ℝ)^67 ≤ (35188512108653/100000000000000 : ℝ)^51 := by
    have hnat : (4515679143 : ℕ)^67*100000000000000^51 ≤ 35188512108653^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515679143 10000000000 35188512108653 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866019403/2000000000 : ℝ), (16606829/40000000 : ℝ), (4515679143/10000000000 : ℝ)] ![(6660206001233/20000000000000 : ℝ), (31510457867243/100000000000000 : ℝ), (35188512108653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866019403/2000000000 : ℝ)|^67 ≤ (6660206001233/20000000000000 : ℝ)^51
        have hw : |(866019403/2000000000 : ℝ)|=(866019403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16606829/40000000 : ℝ)|^67 ≤ (31510457867243/100000000000000 : ℝ)^51
        have hw : |(16606829/40000000 : ℝ)|=(16606829/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4515679143/10000000000 : ℝ)|^67 ≤ (35188512108653/100000000000000 : ℝ)^51
        have hw : |(4515679143/10000000000 : ℝ)|=(4515679143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s4_4 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2055810423/10000000000 : ℝ)*x 0 + (1310551899/2500000000 : ℝ)*x 1 + (5415603643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055810423/10000000000 : ℝ)^67 ≤ (12515503859111/100000000000000 : ℝ)^51 := by
    have hnat : (2055810423 : ℕ)^67*100000000000000^51 ≤ 12515503859111^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055810423 10000000000 12515503859111 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310551899/2500000000 : ℝ)^67 ≤ (5350922835231/12500000000000 : ℝ)^51 := by
    have hnat : (1310551899 : ℕ)^67*12500000000000^51 ≤ 5350922835231^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310551899 2500000000 5350922835231 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415603643/10000000000 : ℝ)^67 ≤ (22338556725941/50000000000000 : ℝ)^51 := by
    have hnat : (5415603643 : ℕ)^67*50000000000000^51 ≤ 22338556725941^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415603643 10000000000 22338556725941 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2055810423/10000000000 : ℝ), (1310551899/2500000000 : ℝ), (5415603643/10000000000 : ℝ)] ![(12515503859111/100000000000000 : ℝ), (5350922835231/12500000000000 : ℝ), (22338556725941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2055810423/10000000000 : ℝ)|^67 ≤ (12515503859111/100000000000000 : ℝ)^51
        have hw : |(-2055810423/10000000000 : ℝ)|=(2055810423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310551899/2500000000 : ℝ)|^67 ≤ (5350922835231/12500000000000 : ℝ)^51
        have hw : |(1310551899/2500000000 : ℝ)|=(1310551899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415603643/10000000000 : ℝ)|^67 ≤ (22338556725941/50000000000000 : ℝ)^51
        have hw : |(5415603643/10000000000 : ℝ)|=(5415603643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s4_5 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5305032401/10000000000 : ℝ)*x 0 + (-78833063/400000000 : ℝ)*x 1 + (2707801821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305032401/10000000000 : ℝ)^67 ≤ (5435326964361/12500000000000 : ℝ)^51 := by
    have hnat : (5305032401 : ℕ)^67*12500000000000^51 ≤ 5435326964361^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305032401 10000000000 5435326964361 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78833063/400000000 : ℝ)^67 ≤ (5920135414287/50000000000000 : ℝ)^51 := by
    have hnat : (78833063 : ℕ)^67*50000000000000^51 ≤ 5920135414287^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78833063 400000000 5920135414287 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707801821/5000000000 : ℝ)^67 ≤ (11169278360261/25000000000000 : ℝ)^51 := by
    have hnat : (2707801821 : ℕ)^67*25000000000000^51 ≤ 11169278360261^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707801821 5000000000 11169278360261 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305032401/10000000000 : ℝ), (-78833063/400000000 : ℝ), (2707801821/5000000000 : ℝ)] ![(5435326964361/12500000000000 : ℝ), (5920135414287/50000000000000 : ℝ), (11169278360261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305032401/10000000000 : ℝ)|^67 ≤ (5435326964361/12500000000000 : ℝ)^51
        have hw : |(5305032401/10000000000 : ℝ)|=(5305032401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-78833063/400000000 : ℝ)|^67 ≤ (5920135414287/50000000000000 : ℝ)^51
        have hw : |(-78833063/400000000 : ℝ)|=(78833063/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707801821/5000000000 : ℝ)|^67 ≤ (11169278360261/25000000000000 : ℝ)^51
        have hw : |(2707801821/5000000000 : ℝ)|=(2707801821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s4_6 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (165782263/312500000 : ℝ)*x 0 + (5415603623/10000000000 : ℝ)*x 1 + (-1970826581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165782263/312500000 : ℝ)^67 ≤ (43482615876407/100000000000000 : ℝ)^51 := by
    have hnat : (165782263 : ℕ)^67*100000000000000^51 ≤ 43482615876407^51*312500000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165782263 312500000 43482615876407 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415603623/10000000000 : ℝ)^67 ≤ (357416905881/800000000000 : ℝ)^51 := by
    have hnat : (5415603623 : ℕ)^67*800000000000^51 ≤ 357416905881^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415603623 10000000000 357416905881 800000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1970826581/10000000000 : ℝ)^67 ≤ (11840270875929/100000000000000 : ℝ)^51 := by
    have hnat : (1970826581 : ℕ)^67*100000000000000^51 ≤ 11840270875929^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1970826581 10000000000 11840270875929 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165782263/312500000 : ℝ), (5415603623/10000000000 : ℝ), (-1970826581/10000000000 : ℝ)] ![(43482615876407/100000000000000 : ℝ), (357416905881/800000000000 : ℝ), (11840270875929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165782263/312500000 : ℝ)|^67 ≤ (43482615876407/100000000000000 : ℝ)^51
        have hw : |(165782263/312500000 : ℝ)|=(165782263/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415603623/10000000000 : ℝ)|^67 ≤ (357416905881/800000000000 : ℝ)^51
        have hw : |(5415603623/10000000000 : ℝ)|=(5415603623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1970826581/10000000000 : ℝ)|^67 ≤ (11840270875929/100000000000000 : ℝ)^51
        have hw : |(-1970826581/10000000000 : ℝ)|=(1970826581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s4_7 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2165062613/5000000000 : ℝ)*x 0 + (451433597/1000000000 : ℝ)*x 1 + (4153057587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165062613/5000000000 : ℝ)^67 ≤ (33301315031583/100000000000000 : ℝ)^51 := by
    have hnat : (2165062613 : ℕ)^67*100000000000000^51 ≤ 33301315031583^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165062613 5000000000 33301315031583 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (451433597/1000000000 : ℝ)^67 ≤ (7034952475907/20000000000000 : ℝ)^51 := by
    have hnat : (451433597 : ℕ)^67*20000000000000^51 ≤ 7034952475907^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451433597 1000000000 7034952475907 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4153057587/10000000000 : ℝ)^67 ≤ (7880980643821/25000000000000 : ℝ)^51 := by
    have hnat : (4153057587 : ℕ)^67*25000000000000^51 ≤ 7880980643821^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153057587 10000000000 7880980643821 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165062613/5000000000 : ℝ), (451433597/1000000000 : ℝ), (4153057587/10000000000 : ℝ)] ![(33301315031583/100000000000000 : ℝ), (7034952475907/20000000000000 : ℝ), (7880980643821/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165062613/5000000000 : ℝ)|^67 ≤ (33301315031583/100000000000000 : ℝ)^51
        have hw : |(2165062613/5000000000 : ℝ)|=(2165062613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(451433597/1000000000 : ℝ)|^67 ≤ (7034952475907/20000000000000 : ℝ)^51
        have hw : |(451433597/1000000000 : ℝ)|=(451433597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4153057587/10000000000 : ℝ)|^67 ≤ (7880980643821/25000000000000 : ℝ)^51
        have hw : |(4153057587/10000000000 : ℝ)|=(4153057587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1328_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (553/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1081/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1081/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1081/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1081/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1081/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1081/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1081/10000 : ℝ) ^ (4287/1024 : ℝ) ≤ (9017551328392363/100000000000000000000 : ℝ) := by
    have hpowers : (1081/10000 : ℝ)^4287 ≤ (9017551328392363/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1081 : ℕ)^4287*100000000000000000000^1024 ≤ 9017551328392363^1024*10000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1081 10000 9017551328392363 100000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1081/10000 : ℝ)) (X := (9017551328392363/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15023/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (17883087313990871/50000000000000000000 : ℝ) := by
    have hpowers : (15023/100000 : ℝ)^4287 ≤ (17883087313990871/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15023 : ℕ)^4287*50000000000000000000^1024 ≤ 17883087313990871^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15023 100000 17883087313990871 50000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15023/100000 : ℝ)) (X := (17883087313990871/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009017551328392363/50000000000000000000 : ℝ) ≤ (10000430759918081/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50009017551328392363/50000000000000000000 : ℝ)^1024 ≤ (10000430759918081/10000000000000000 : ℝ)^4287 := by
      have hnat : (50009017551328392363 : ℕ)^1024*10000000000000000^4287 ≤ 10000430759918081^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009017551328392363 50000000000000000000 10000430759918081 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000430759918081/10000000000000000 : ℝ)) (X := (50009017551328392363/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008956745191274821/20000000000000000000 : ℝ) ≤ (10001069529312419/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (20008956745191274821/20000000000000000000 : ℝ)^1024 ≤ (10001069529312419/10000000000000000 : ℝ)^4287 := by
      have hnat : (20008956745191274821 : ℕ)^1024*10000000000000000^4287 ≤ 10001069529312419^4287*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008956745191274821 20000000000000000000 10001069529312419 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001069529312419/10000000000000000 : ℝ)) (X := (20008956745191274821/20000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017883087313990871/25000000000000000000 : ℝ) ≤ (10001708298706757/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (25017883087313990871/25000000000000000000 : ℝ)^1024 ≤ (10001708298706757/10000000000000000 : ℝ)^4287 := by
      have hnat : (25017883087313990871 : ℕ)^1024*10000000000000000^4287 ≤ 10001708298706757^4287*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017883087313990871 25000000000000000000 10001708298706757 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001708298706757/10000000000000000 : ℝ)) (X := (25017883087313990871/25000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9017551328392363/100000000000000000000 : ℝ) ≤ ((42118004597229287693/42130000000000000000 : ℝ)+2*(319384697169/210650000000000 : ℝ)*(1081/10000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (42118004597229287693/42130000000000000000 : ℝ)+2*(319384697169/210650000000000 : ℝ)*(1081/10000 : ℝ)=(10000430759918081/10000000000000000 : ℝ) by norm_num, show 1+2*(9017551328392363/100000000000000000000 : ℝ)=(50009017551328392363/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17883087313990871/50000000000000000000 : ℝ)+(9017551328392363/100000000000000000000 : ℝ) ≤ ((42118004597229287693/42130000000000000000 : ℝ)+(319384697169/210650000000000 : ℝ)*((15023/100000 : ℝ)+(1081/10000 : ℝ)))^(4287/1024 : ℝ) := by
    rw [show (42118004597229287693/42130000000000000000 : ℝ)+(319384697169/210650000000000 : ℝ)*((15023/100000 : ℝ)+(1081/10000 : ℝ))=(10001069529312419/10000000000000000 : ℝ) by norm_num, show 1+(17883087313990871/50000000000000000000 : ℝ)+(9017551328392363/100000000000000000000 : ℝ)=(20008956745191274821/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17883087313990871/50000000000000000000 : ℝ) ≤ ((42118004597229287693/42130000000000000000 : ℝ)+2*(319384697169/210650000000000 : ℝ)*(15023/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (42118004597229287693/42130000000000000000 : ℝ)+2*(319384697169/210650000000000 : ℝ)*(15023/100000 : ℝ)=(10001708298706757/10000000000000000 : ℝ) by norm_num, show 1+2*(17883087313990871/50000000000000000000 : ℝ)=(25017883087313990871/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42118004597229287693/42130000000000000000 : ℝ)*(X 1 0+X 2 0)+(319384697169/210650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (1081/10000 : ℝ)) (hi := (15023/100000 : ℝ)) (c := (42118004597229287693/42130000000000000000 : ℝ)) (alpha := (319384697169/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42118004597229287693/42130000000000000000 : ℝ)*(X 0 1+X 2 1)+(319384697169/210650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (1081/10000 : ℝ)) (hi := (15023/100000 : ℝ)) (c := (42118004597229287693/42130000000000000000 : ℝ)) (alpha := (319384697169/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42118004597229287693/42130000000000000000 : ℝ)*(X 0 2+X 1 2)+(319384697169/210650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (1081/10000 : ℝ)) (hi := (15023/100000 : ℝ)) (c := (42118004597229287693/42130000000000000000 : ℝ)) (alpha := (319384697169/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2055796781/10000000000 : ℝ)*X 0 0+(1083250317/2000000000 : ℝ)*X 0 1+(104831263/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349954917/10000000000 : ℝ)*X 1 0+(-1072433503/5000000000 : ℝ)*X 1 1+(5241563031/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349954983/10000000000 : ℝ)*X 2 0+(131039069/250000000 : ℝ)*X 2 1+(-2144867277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((866019403/2000000000 : ℝ)*X 0 0+(16606829/40000000 : ℝ)*X 0 1+(4515679143/10000000000 : ℝ)*X 0 2+(866019403/2000000000 : ℝ)*X 1 0+(16606829/40000000 : ℝ)*X 1 1+(4515679143/10000000000 : ℝ)*X 1 2+(866019403/2000000000 : ℝ)*X 2 0+(16606829/40000000 : ℝ)*X 2 1+(4515679143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2055810423/10000000000 : ℝ)*X 0 0+(1310551899/2500000000 : ℝ)*X 0 1+(5415603643/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305032401/10000000000 : ℝ)*X 1 0+(-78833063/400000000 : ℝ)*X 1 1+(2707801821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165782263/312500000 : ℝ)*X 2 0+(5415603623/10000000000 : ℝ)*X 2 1+(-1970826581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165062613/5000000000 : ℝ)*X 0 0+(451433597/1000000000 : ℝ)*X 0 1+(4153057587/10000000000 : ℝ)*X 0 2+(2165062613/5000000000 : ℝ)*X 1 0+(451433597/1000000000 : ℝ)*X 1 1+(4153057587/10000000000 : ℝ)*X 1 2+(2165062613/5000000000 : ℝ)*X 2 0+(451433597/1000000000 : ℝ)*X 2 1+(4153057587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8811620080206338009112339753/2106500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189011533/20000000000000 : ℝ)*(base19) + (46208893/4000000000000 : ℝ)*(base23) + (66312471/50000000000000 : ℝ)*(upper3) + (41290513/50000000000000 : ℝ)*(lower4) + (4235999674744731/100000000000000 : ℝ)*(major0) + (4235999674744731/100000000000000 : ℝ)*(major1) + (4235999674744731/100000000000000 : ℝ)*(major2) + (5724497802809631/100000000000000 : ℝ)*(sp0) + (2862255581036183/50000000000000 : ℝ)*(sp1) + (2862254593807817/50000000000000 : ℝ)*(sp2) + (2747475224838009/100000000000000 : ℝ)*(sp3) + (14304320401/100000000000000 : ℝ)*(sp4) + (220536509/12500000000000 : ℝ)*(sp6) + (2969521503/25000000000000 : ℝ)*(sp7) + (1373743551462011/50000000000000 : ℝ)*(f.failure) + (5724512107130031/100000000000000 : ℝ)*(f.sum) + (42384209826767/21065000000000000000000000000 : ℝ)*base66 + (36192473287569695583/4213000000000000000000000000000000 : ℝ)*base67 + (26970469897530695583/4213000000000000000000000000000000 : ℝ)*base69 + (41740120309145695583/4213000000000000000000000000000000 : ℝ)*base71 + (1257074732123/1316562500000000000000000000 : ℝ)*base73 + (67572065737841695583/4213000000000000000000000000000000 : ℝ)*base75 + (50725242065569695583/4213000000000000000000000000000000 : ℝ)*base77 + (17551694302224695583/4213000000000000000000000000000000 : ℝ)*base79 + (10503675814813/21065000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (16245399/1250000000000000000000 : ℝ)*base89 + (16245399/1250000000000000000000 : ℝ)*base91 + (16245399/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (973509403390918998649410093/263312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (332893081/50000000000000 : ℝ)*(base19) + (181203779/25000000000000 : ℝ)*(base23) + (3009827/4000000000000 : ℝ)*(upper3) + (1037997/5000000000000 : ℝ)*(lower4) + (83808511/100000000000000 : ℝ)*(upper5) + (533443292204767/12500000000000 : ℝ)*(major0) + (533443292204767/12500000000000 : ℝ)*(major1) + (533443292204767/12500000000000 : ℝ)*(major2) + (3295213341/25000000000000 : ℝ)*(sp1) + (13604767381/100000000000000 : ℝ)*(sp2) + (5767144151640589/100000000000000 : ℝ)*(sp4) + (720891288125133/12500000000000 : ℝ)*(sp5) + (1441782455514523/25000000000000 : ℝ)*(sp6) + (2767948400396889/100000000000000 : ℝ)*(sp7) + (2767948400396889/100000000000000 : ℝ)*(f.failure) + (5767144151640589/100000000000000 : ℝ)*(f.sum) + (64402553587113/21065000000000000000000000000 : ℝ)*base65 + (371562243999117469/526625000000000000000000000000000 : ℝ)*base68 + (4952357773842617469/526625000000000000000000000000000 : ℝ)*base70 + (1174568736713882531/526625000000000000000000000000000 : ℝ)*base71 + (5534560570239/10532500000000000000000000000 : ℝ)*base73 + (2093624330390742469/526625000000000000000000000000000 : ℝ)*base76 + (4399574856668492469/526625000000000000000000000000000 : ℝ)*base78 + (5133625506348882531/526625000000000000000000000000000 : ℝ)*base79 + (42308251715271/10532500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (12254701/2500000000000000000000 : ℝ)*base89 + (12254701/2500000000000000000000 : ℝ)*base91 + (12254701/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1328_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1081/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1328_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1328_s5_0 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056074393/10000000000 : ℝ)*x 0 + (1082773017/2000000000 : ℝ)*x 1 + (5243767033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056074393/10000000000 : ℝ)^67 ≤ (3129403769449/25000000000000 : ℝ)^51 := by
    have hnat : (2056074393 : ℕ)^67*25000000000000^51 ≤ 3129403769449^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056074393 10000000000 3129403769449 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082773017/2000000000 : ℝ)^67 ≤ (44658272181907/100000000000000 : ℝ)^51 := by
    have hnat : (1082773017 : ℕ)^67*100000000000000^51 ≤ 44658272181907^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082773017 2000000000 44658272181907 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243767033/10000000000 : ℝ)^67 ≤ (2676507045609/6250000000000 : ℝ)^51 := by
    have hnat : (5243767033 : ℕ)^67*6250000000000^51 ≤ 2676507045609^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243767033 10000000000 2676507045609 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056074393/10000000000 : ℝ), (1082773017/2000000000 : ℝ), (5243767033/10000000000 : ℝ)] ![(3129403769449/25000000000000 : ℝ), (44658272181907/100000000000000 : ℝ), (2676507045609/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056074393/10000000000 : ℝ)|^67 ≤ (3129403769449/25000000000000 : ℝ)^51
        have hw : |(-2056074393/10000000000 : ℝ)|=(2056074393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082773017/2000000000 : ℝ)|^67 ≤ (44658272181907/100000000000000 : ℝ)^51
        have hw : |(1082773017/2000000000 : ℝ)|=(1082773017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243767033/10000000000 : ℝ)|^67 ≤ (2676507045609/6250000000000 : ℝ)^51
        have hw : |(5243767033/10000000000 : ℝ)|=(5243767033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s5_1 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (106986927/200000000 : ℝ)*x 0 + (-535690001/2500000000 : ℝ)*x 1 + (1048753407/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106986927/200000000 : ℝ)^67 ≤ (43960409288479/100000000000000 : ℝ)^51 := by
    have hnat : (106986927 : ℕ)^67*100000000000000^51 ≤ 43960409288479^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106986927 200000000 43960409288479 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (535690001/2500000000 : ℝ)^67 ≤ (330386948869/2500000000000 : ℝ)^51 := by
    have hnat : (535690001 : ℕ)^67*2500000000000^51 ≤ 330386948869^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535690001 2500000000 330386948869 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048753407/2000000000 : ℝ)^67 ≤ (42824112751201/100000000000000 : ℝ)^51 := by
    have hnat : (1048753407 : ℕ)^67*100000000000000^51 ≤ 42824112751201^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048753407 2000000000 42824112751201 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106986927/200000000 : ℝ), (-535690001/2500000000 : ℝ), (1048753407/2000000000 : ℝ)] ![(43960409288479/100000000000000 : ℝ), (330386948869/2500000000000 : ℝ), (42824112751201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106986927/200000000 : ℝ)|^67 ≤ (43960409288479/100000000000000 : ℝ)^51
        have hw : |(106986927/200000000 : ℝ)|=(106986927/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-535690001/2500000000 : ℝ)|^67 ≤ (330386948869/2500000000000 : ℝ)^51
        have hw : |(-535690001/2500000000 : ℝ)|=(535690001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048753407/2000000000 : ℝ)|^67 ≤ (42824112751201/100000000000000 : ℝ)^51
        have hw : |(1048753407/2000000000 : ℝ)|=(1048753407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s5_2 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5349346369/10000000000 : ℝ)*x 0 + (5243767029/10000000000 : ℝ)*x 1 + (-1071379993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349346369/10000000000 : ℝ)^67 ≤ (8792081898721/20000000000000 : ℝ)^51 := by
    have hnat : (5349346369 : ℕ)^67*20000000000000^51 ≤ 8792081898721^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349346369 10000000000 8792081898721 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243767029/10000000000 : ℝ)^67 ≤ (42824112686829/100000000000000 : ℝ)^51 := by
    have hnat : (5243767029 : ℕ)^67*100000000000000^51 ≤ 42824112686829^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243767029 10000000000 42824112686829 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071379993/5000000000 : ℝ)^67 ≤ (3303869452229/25000000000000 : ℝ)^51 := by
    have hnat : (1071379993 : ℕ)^67*25000000000000^51 ≤ 3303869452229^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071379993 5000000000 3303869452229 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349346369/10000000000 : ℝ), (5243767029/10000000000 : ℝ), (-1071379993/5000000000 : ℝ)] ![(8792081898721/20000000000000 : ℝ), (42824112686829/100000000000000 : ℝ), (3303869452229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349346369/10000000000 : ℝ)|^67 ≤ (8792081898721/20000000000000 : ℝ)^51
        have hw : |(5349346369/10000000000 : ℝ)|=(5349346369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243767029/10000000000 : ℝ)|^67 ≤ (42824112686829/100000000000000 : ℝ)^51
        have hw : |(5243767029/10000000000 : ℝ)|=(5243767029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1071379993/5000000000 : ℝ)|^67 ≤ (3303869452229/25000000000000 : ℝ)^51
        have hw : |(-1071379993/5000000000 : ℝ)|=(1071379993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s5_3 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4330262719/10000000000 : ℝ)*x 0 + (2078234559/5000000000 : ℝ)*x 1 + (902175201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330262719/10000000000 : ℝ)^67 ≤ (16651352089451/50000000000000 : ℝ)^51 := by
    have hnat : (4330262719 : ℕ)^67*50000000000000^51 ≤ 16651352089451^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330262719 10000000000 16651352089451 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2078234559/5000000000 : ℝ)^67 ≤ (3155794632653/10000000000000 : ℝ)^51 := by
    have hnat : (2078234559 : ℕ)^67*10000000000000^51 ≤ 3155794632653^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078234559 5000000000 3155794632653 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902175201/2000000000 : ℝ)^67 ≤ (1098104671469/3125000000000 : ℝ)^51 := by
    have hnat : (902175201 : ℕ)^67*3125000000000^51 ≤ 1098104671469^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902175201 2000000000 1098104671469 3125000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330262719/10000000000 : ℝ), (2078234559/5000000000 : ℝ), (902175201/2000000000 : ℝ)] ![(16651352089451/50000000000000 : ℝ), (3155794632653/10000000000000 : ℝ), (1098104671469/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330262719/10000000000 : ℝ)|^67 ≤ (16651352089451/50000000000000 : ℝ)^51
        have hw : |(4330262719/10000000000 : ℝ)|=(4330262719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2078234559/5000000000 : ℝ)|^67 ≤ (3155794632653/10000000000000 : ℝ)^51
        have hw : |(2078234559/5000000000 : ℝ)|=(2078234559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902175201/2000000000 : ℝ)|^67 ≤ (1098104671469/3125000000000 : ℝ)^51
        have hw : |(902175201/2000000000 : ℝ)|=(902175201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s5_4 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028043451/5000000000 : ℝ)*x 0 + (2622189163/5000000000 : ℝ)*x 1 + (5413250629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028043451/5000000000 : ℝ)^67 ≤ (6258857563127/50000000000000 : ℝ)^51 := by
    have hnat : (1028043451 : ℕ)^67*50000000000000^51 ≤ 6258857563127^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028043451 5000000000 6258857563127 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622189163/5000000000 : ℝ)^67 ≤ (2141533563339/5000000000000 : ℝ)^51 := by
    have hnat : (2622189163 : ℕ)^67*5000000000000^51 ≤ 2141533563339^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622189163 5000000000 2141533563339 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413250629/10000000000 : ℝ)^67 ≤ (22325806796743/50000000000000 : ℝ)^51 := by
    have hnat : (5413250629 : ℕ)^67*50000000000000^51 ≤ 22325806796743^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413250629 10000000000 22325806796743 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028043451/5000000000 : ℝ), (2622189163/5000000000 : ℝ), (5413250629/10000000000 : ℝ)] ![(6258857563127/50000000000000 : ℝ), (2141533563339/5000000000000 : ℝ), (22325806796743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028043451/5000000000 : ℝ)|^67 ≤ (6258857563127/50000000000000 : ℝ)^51
        have hw : |(-1028043451/5000000000 : ℝ)|=(1028043451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622189163/5000000000 : ℝ)|^67 ≤ (2141533563339/5000000000000 : ℝ)^51
        have hw : |(2622189163/5000000000 : ℝ)|=(2622189163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413250629/10000000000 : ℝ)|^67 ≤ (22325806796743/50000000000000 : ℝ)^51
        have hw : |(5413250629/10000000000 : ℝ)|=(5413250629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s5_5 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5305604533/10000000000 : ℝ)*x 0 + (-197327639/1000000000 : ℝ)*x 1 + (5413250629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305604533/10000000000 : ℝ)^67 ≤ (43488776496769/100000000000000 : ℝ)^51 := by
    have hnat : (5305604533 : ℕ)^67*100000000000000^51 ≤ 43488776496769^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305604533 10000000000 43488776496769 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197327639/1000000000 : ℝ)^67 ≤ (11859609907771/100000000000000 : ℝ)^51 := by
    have hnat : (197327639 : ℕ)^67*100000000000000^51 ≤ 11859609907771^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197327639 1000000000 11859609907771 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413250629/10000000000 : ℝ)^67 ≤ (22325806796743/50000000000000 : ℝ)^51 := by
    have hnat : (5413250629 : ℕ)^67*50000000000000^51 ≤ 22325806796743^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413250629 10000000000 22325806796743 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305604533/10000000000 : ℝ), (-197327639/1000000000 : ℝ), (5413250629/10000000000 : ℝ)] ![(43488776496769/100000000000000 : ℝ), (11859609907771/100000000000000 : ℝ), (22325806796743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305604533/10000000000 : ℝ)|^67 ≤ (43488776496769/100000000000000 : ℝ)^51
        have hw : |(5305604533/10000000000 : ℝ)|=(5305604533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197327639/1000000000 : ℝ)|^67 ≤ (11859609907771/100000000000000 : ℝ)^51
        have hw : |(-197327639/1000000000 : ℝ)|=(197327639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413250629/10000000000 : ℝ)|^67 ≤ (22325806796743/50000000000000 : ℝ)^51
        have hw : |(5413250629/10000000000 : ℝ)|=(5413250629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s5_6 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5305604519/10000000000 : ℝ)*x 0 + (2706625321/5000000000 : ℝ)*x 1 + (-197327639/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305604519/10000000000 : ℝ)^67 ≤ (10872194086503/25000000000000 : ℝ)^51 := by
    have hnat : (5305604519 : ℕ)^67*25000000000000^51 ≤ 10872194086503^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305604519 10000000000 10872194086503 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706625321/5000000000 : ℝ)^67 ≤ (44651613734359/100000000000000 : ℝ)^51 := by
    have hnat : (2706625321 : ℕ)^67*100000000000000^51 ≤ 44651613734359^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706625321 5000000000 44651613734359 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197327639/1000000000 : ℝ)^67 ≤ (11859609907771/100000000000000 : ℝ)^51 := by
    have hnat : (197327639 : ℕ)^67*100000000000000^51 ≤ 11859609907771^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197327639 1000000000 11859609907771 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305604519/10000000000 : ℝ), (2706625321/5000000000 : ℝ), (-197327639/1000000000 : ℝ)] ![(10872194086503/25000000000000 : ℝ), (44651613734359/100000000000000 : ℝ), (11859609907771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305604519/10000000000 : ℝ)|^67 ≤ (10872194086503/25000000000000 : ℝ)^51
        have hw : |(5305604519/10000000000 : ℝ)|=(5305604519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706625321/5000000000 : ℝ)|^67 ≤ (44651613734359/100000000000000 : ℝ)^51
        have hw : |(2706625321/5000000000 : ℝ)|=(2706625321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197327639/1000000000 : ℝ)|^67 ≤ (11859609907771/100000000000000 : ℝ)^51
        have hw : |(-197327639/1000000000 : ℝ)|=(197327639/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1328_s5_7 (p : ℝ) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4330288757/10000000000 : ℝ)*x 0 + (2254801191/5000000000 : ℝ)*x 1 + (1039437341/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330288757/10000000000 : ℝ)^67 ≤ (33302967252893/100000000000000 : ℝ)^51 := by
    have hnat : (4330288757 : ℕ)^67*100000000000000^51 ≤ 33302967252893^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330288757 10000000000 33302967252893 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254801191/5000000000 : ℝ)^67 ≤ (35126316045369/100000000000000 : ℝ)^51 := by
    have hnat : (2254801191 : ℕ)^67*100000000000000^51 ≤ 35126316045369^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254801191 5000000000 35126316045369 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039437341/2500000000 : ℝ)^67 ≤ (6314143337719/20000000000000 : ℝ)^51 := by
    have hnat : (1039437341 : ℕ)^67*20000000000000^51 ≤ 6314143337719^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039437341 2500000000 6314143337719 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330288757/10000000000 : ℝ), (2254801191/5000000000 : ℝ), (1039437341/2500000000 : ℝ)] ![(33302967252893/100000000000000 : ℝ), (35126316045369/100000000000000 : ℝ), (6314143337719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330288757/10000000000 : ℝ)|^67 ≤ (33302967252893/100000000000000 : ℝ)^51
        have hw : |(4330288757/10000000000 : ℝ)|=(4330288757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254801191/5000000000 : ℝ)|^67 ≤ (35126316045369/100000000000000 : ℝ)^51
        have hw : |(2254801191/5000000000 : ℝ)|=(2254801191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1039437341/2500000000 : ℝ)|^67 ≤ (6314143337719/20000000000000 : ℝ)^51
        have hw : |(1039437341/2500000000 : ℝ)|=(1039437341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1328_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11107/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14707/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (553/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (553/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (553/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (553/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (553/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (553/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (553/5000 : ℝ) ^ (4287/1024 : ℝ) ≤ (4961676344940649/50000000000000000000 : ℝ) := by
    have hpowers : (553/5000 : ℝ)^4287 ≤ (4961676344940649/50000000000000000000 : ℝ)^1024 := by
      have hnat : (553 : ℕ)^4287*50000000000000000000^1024 ≤ 4961676344940649^1024*5000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        553 5000 4961676344940649 50000000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (553/5000 : ℝ)) (X := (4961676344940649/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (4287/1024 : ℝ) ≤ (829718899393011/2500000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^4287 ≤ (829718899393011/2500000000000000000 : ℝ)^1024 := by
      have hnat : (14757 : ℕ)^4287*2500000000000000000^1024 ≤ 829718899393011^1024*100000^4287 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 829718899393011 2500000000000000000 4287 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (829718899393011/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004961676344940649/25000000000000000000 : ℝ) ≤ (10000474025926769/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (25004961676344940649/25000000000000000000 : ℝ)^1024 ≤ (10000474025926769/10000000000000000 : ℝ)^4287 := by
      have hnat : (25004961676344940649 : ℕ)^1024*10000000000000000^4287 ≤ 10000474025926769^4287*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004961676344940649 25000000000000000000 10000474025926769 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000474025926769/10000000000000000 : ℝ)) (X := (25004961676344940649/25000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021556054332800869/50000000000000000000 : ℝ) ≤ (2500257403533237/2500000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (50021556054332800869/50000000000000000000 : ℝ)^1024 ≤ (2500257403533237/2500000000000000 : ℝ)^4287 := by
      have hnat : (50021556054332800869 : ℕ)^1024*2500000000000000^4287 ≤ 2500257403533237^4287*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021556054332800869 50000000000000000000 2500257403533237 2500000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500257403533237/2500000000000000 : ℝ)) (X := (50021556054332800869/50000000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1250829718899393011/1250000000000000000 : ℝ) ≤ (10001585202339127/10000000000000000 : ℝ) ^ (4287/1024 : ℝ) := by
    have hpowers : (1250829718899393011/1250000000000000000 : ℝ)^1024 ≤ (10001585202339127/10000000000000000 : ℝ)^4287 := by
      have hnat : (1250829718899393011 : ℕ)^1024*10000000000000000^4287 ≤ 10001585202339127^4287*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250829718899393011 1250000000000000000 10001585202339127 10000000000000000 1024 4287 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001585202339127/10000000000000000 : ℝ)) (X := (1250829718899393011/1250000000000000000 : ℝ)) (by norm_num) 4287 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4961676344940649/50000000000000000000 : ℝ) ≤ ((36959462862730585513/36970000000000000000 : ℝ)+2*(555588206179/369700000000000 : ℝ)*(553/5000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (36959462862730585513/36970000000000000000 : ℝ)+2*(555588206179/369700000000000 : ℝ)*(553/5000 : ℝ)=(10000474025926769/10000000000000000 : ℝ) by norm_num, show 1+2*(4961676344940649/50000000000000000000 : ℝ)=(25004961676344940649/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(829718899393011/2500000000000000000 : ℝ)+(4961676344940649/50000000000000000000 : ℝ) ≤ ((36959462862730585513/36970000000000000000 : ℝ)+(555588206179/369700000000000 : ℝ)*((14757/100000 : ℝ)+(553/5000 : ℝ)))^(4287/1024 : ℝ) := by
    rw [show (36959462862730585513/36970000000000000000 : ℝ)+(555588206179/369700000000000 : ℝ)*((14757/100000 : ℝ)+(553/5000 : ℝ))=(2500257403533237/2500000000000000 : ℝ) by norm_num, show 1+(829718899393011/2500000000000000000 : ℝ)+(4961676344940649/50000000000000000000 : ℝ)=(50021556054332800869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(829718899393011/2500000000000000000 : ℝ) ≤ ((36959462862730585513/36970000000000000000 : ℝ)+2*(555588206179/369700000000000 : ℝ)*(14757/100000 : ℝ))^(4287/1024 : ℝ) := by
    rw [show (36959462862730585513/36970000000000000000 : ℝ)+2*(555588206179/369700000000000 : ℝ)*(14757/100000 : ℝ)=(10001585202339127/10000000000000000 : ℝ) by norm_num, show 1+2*(829718899393011/2500000000000000000 : ℝ)=(1250829718899393011/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36959462862730585513/36970000000000000000 : ℝ)*(X 1 0+X 2 0)+(555588206179/369700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (36959462862730585513/36970000000000000000 : ℝ)) (alpha := (555588206179/369700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36959462862730585513/36970000000000000000 : ℝ)*(X 0 1+X 2 1)+(555588206179/369700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (36959462862730585513/36970000000000000000 : ℝ)) (alpha := (555588206179/369700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36959462862730585513/36970000000000000000 : ℝ)*(X 0 2+X 1 2)+(555588206179/369700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4287/1024 : ℝ)) (lo := (553/5000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (36959462862730585513/36970000000000000000 : ℝ)) (alpha := (555588206179/369700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2056074393/10000000000 : ℝ)*X 0 0+(1082773017/2000000000 : ℝ)*X 0 1+(5243767033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106986927/200000000 : ℝ)*X 1 0+(-535690001/2500000000 : ℝ)*X 1 1+(1048753407/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349346369/10000000000 : ℝ)*X 2 0+(5243767029/10000000000 : ℝ)*X 2 1+(-1071379993/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330262719/10000000000 : ℝ)*X 0 0+(2078234559/5000000000 : ℝ)*X 0 1+(902175201/2000000000 : ℝ)*X 0 2+(4330262719/10000000000 : ℝ)*X 1 0+(2078234559/5000000000 : ℝ)*X 1 1+(902175201/2000000000 : ℝ)*X 1 2+(4330262719/10000000000 : ℝ)*X 2 0+(2078234559/5000000000 : ℝ)*X 2 1+(902175201/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1028043451/5000000000 : ℝ)*X 0 0+(2622189163/5000000000 : ℝ)*X 0 1+(5413250629/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305604533/10000000000 : ℝ)*X 1 0+(-197327639/1000000000 : ℝ)*X 1 1+(5413250629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305604519/10000000000 : ℝ)*X 2 0+(2706625321/5000000000 : ℝ)*X 2 1+(-197327639/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4330288757/10000000000 : ℝ)*X 0 0+(2254801191/5000000000 : ℝ)*X 0 1+(1039437341/2500000000 : ℝ)*X 0 2+(4330288757/10000000000 : ℝ)*X 1 0+(2254801191/5000000000 : ℝ)*X 1 1+(1039437341/2500000000 : ℝ)*X 1 2+(4330288757/10000000000 : ℝ)*X 2 0+(2254801191/5000000000 : ℝ)*X 2 1+(1039437341/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1328_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9646748233734335349968731947/1848500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62296299/6250000000000 : ℝ)*(base19) + (118224099/12500000000000 : ℝ)*(base23) + (38423951/100000000000000 : ℝ)*(lower2) + (63287467/50000000000000 : ℝ)*(upper3) + (49301279/50000000000000 : ℝ)*(upper5) + (4350319276151473/100000000000000 : ℝ)*(major0) + (4350319276151473/100000000000000 : ℝ)*(major1) + (4350319276151473/100000000000000 : ℝ)*(major2) + (2939491265582813/50000000000000 : ℝ)*(sp0) + (5879002107153591/100000000000000 : ℝ)*(sp1) + (367437634881349/6250000000000 : ℝ)*(sp2) + (1410812504381659/50000000000000 : ℝ)*(sp3) + (20572728749/100000000000000 : ℝ)*(sp4) + (10265688919/100000000000000 : ℝ)*(sp7) + (2821635274452237/100000000000000 : ℝ)*(f.failure) + (9406404966231/160000000000 : ℝ)*(f.sum) + (32223784452901/9242500000000000000000000000 : ℝ)*base65 + (9969413162432110649/3697000000000000000000000000000000 : ℝ)*base67 + (39112113812110889351/3697000000000000000000000000000000 : ℝ)*base70 + (14876228049240889351/3697000000000000000000000000000000 : ℝ)*base72 + (68242918181937/18485000000000000000000000000 : ℝ)*base73 + (12181065568592889351/3697000000000000000000000000000000 : ℝ)*base76 + (16924235977497110649/3697000000000000000000000000000000 : ℝ)*base77 + (14155772745311889351/3697000000000000000000000000000000 : ℝ)*base80 + (13353939701103/18485000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3669233/2500000000000000000000 : ℝ)*base89 + (3669233/2500000000000000000000 : ℝ)*base91 + (3669233/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (967842240116143755924481017/369700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (236405023/50000000000000 : ℝ)*(base19) + (487663149/100000000000000 : ℝ)*(base23) + (7175611/12500000000000 : ℝ)*(upper3) + (6747569/50000000000000 : ℝ)*(lower4) + (12947997/25000000000000 : ℝ)*(upper5) + (876372947235799/20000000000000 : ℝ)*(major0) + (876372947235799/20000000000000 : ℝ)*(major1) + (876372947235799/20000000000000 : ℝ)*(major2) + (147010201/1562500000000 : ℝ)*(sp1) + (10020329661/100000000000000 : ℝ)*(sp2) + (5921633593352973/100000000000000 : ℝ)*(sp4) + (370101481993129/6250000000000 : ℝ)*(sp5) + (5921623085360163/100000000000000 : ℝ)*(sp6) + (2842095791741263/100000000000000 : ℝ)*(sp7) + (2842095791741263/100000000000000 : ℝ)*(f.failure) + (5921633593352973/100000000000000 : ℝ)*(f.sum) + (650940952107/462125000000000000000000000 : ℝ)*base65 + (4326070125984879887/739400000000000000000000000000000 : ℝ)*base67 + (5554416798135879887/739400000000000000000000000000000 : ℝ)*base69 + (5040600452088279887/739400000000000000000000000000000 : ℝ)*base71 + (9227543361171/3697000000000000000000000000 : ℝ)*base73 + (2288399394763279887/739400000000000000000000000000000 : ℝ)*base75 + (754135249124679887/739400000000000000000000000000000 : ℝ)*base77 + (4359595544575079887/739400000000000000000000000000000 : ℝ)*base79 + (1087686905931/3697000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (14122267/2500000000000000000000 : ℝ)*base89 + (14122267/2500000000000000000000 : ℝ)*base91 + (14122267/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1328_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (553/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1328_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1328_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (101/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1328_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1328_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1328_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4287/1024 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38544309/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (101/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11107/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1328_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
