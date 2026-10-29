-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1563_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:24:44.359284+00:00
-- url     : https://prove2.me/submissions/d596a0f6-9516-4e9d-8f8f-d6d48727416b

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
theorem support_rectangle_w1563_s0_0 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-326610677/2000000000 : ℝ)*x 0 + (293731319/500000000 : ℝ)*x 1 + (2438266403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (326610677/2000000000 : ℝ)^4623 ≤ (1950340812457/20000000000000 : ℝ)^3599 := by
    have hnat : (326610677 : ℕ)^4623*20000000000000^3599 ≤ 1950340812457^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326610677 2000000000 1950340812457 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (293731319/500000000 : ℝ)^4623 ≤ (50495154872657/100000000000000 : ℝ)^3599 := by
    have hnat : (293731319 : ℕ)^4623*100000000000000^3599 ≤ 50495154872657^3599*500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293731319 500000000 50495154872657 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2438266403/5000000000 : ℝ)^4623 ≤ (39753141052931/100000000000000 : ℝ)^3599 := by
    have hnat : (2438266403 : ℕ)^4623*100000000000000^3599 ≤ 39753141052931^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438266403 5000000000 39753141052931 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-326610677/2000000000 : ℝ), (293731319/500000000 : ℝ), (2438266403/5000000000 : ℝ)] ![(1950340812457/20000000000000 : ℝ), (50495154872657/100000000000000 : ℝ), (39753141052931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-326610677/2000000000 : ℝ)|^4623 ≤ (1950340812457/20000000000000 : ℝ)^3599
        have hw : |(-326610677/2000000000 : ℝ)|=(326610677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(293731319/500000000 : ℝ)|^4623 ≤ (50495154872657/100000000000000 : ℝ)^3599
        have hw : |(293731319/500000000 : ℝ)|=(293731319/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2438266403/5000000000 : ℝ)|^4623 ≤ (39753141052931/100000000000000 : ℝ)^3599
        have hw : |(2438266403/5000000000 : ℝ)|=(2438266403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s0_1 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (546697367/1000000000 : ℝ)*x 0 + (-1094471777/5000000000 : ℝ)*x 1 + (609566601/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546697367/1000000000 : ℝ)^4623 ≤ (23019709869371/50000000000000 : ℝ)^3599 := by
    have hnat : (546697367 : ℕ)^4623*50000000000000^3599 ≤ 23019709869371^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546697367 1000000000 23019709869371 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094471777/5000000000 : ℝ)^4623 ≤ (7103719584271/50000000000000 : ℝ)^3599 := by
    have hnat : (1094471777 : ℕ)^4623*50000000000000^3599 ≤ 7103719584271^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094471777 5000000000 7103719584271 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (609566601/1250000000 : ℝ)^4623 ≤ (19876570536937/50000000000000 : ℝ)^3599 := by
    have hnat : (609566601 : ℕ)^4623*50000000000000^3599 ≤ 19876570536937^3599*1250000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609566601 1250000000 19876570536937 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546697367/1000000000 : ℝ), (-1094471777/5000000000 : ℝ), (609566601/1250000000 : ℝ)] ![(23019709869371/50000000000000 : ℝ), (7103719584271/50000000000000 : ℝ), (19876570536937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546697367/1000000000 : ℝ)|^4623 ≤ (23019709869371/50000000000000 : ℝ)^3599
        have hw : |(546697367/1000000000 : ℝ)|=(546697367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1094471777/5000000000 : ℝ)|^4623 ≤ (7103719584271/50000000000000 : ℝ)^3599
        have hw : |(-1094471777/5000000000 : ℝ)|=(1094471777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(609566601/1250000000 : ℝ)|^4623 ≤ (19876570536937/50000000000000 : ℝ)^3599
        have hw : |(609566601/1250000000 : ℝ)|=(609566601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s0_2 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5466973719/10000000000 : ℝ)*x 0 + (4876532753/10000000000 : ℝ)*x 1 + (-2188943561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5466973719/10000000000 : ℝ)^4623 ≤ (46039420268797/100000000000000 : ℝ)^3599 := by
    have hnat : (5466973719 : ℕ)^4623*100000000000000^3599 ≤ 46039420268797^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466973719 10000000000 46039420268797 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4876532753/10000000000 : ℝ)^4623 ≤ (795062809959/2000000000000 : ℝ)^3599 := by
    have hnat : (4876532753 : ℕ)^4623*2000000000000^3599 ≤ 795062809959^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4876532753 10000000000 795062809959 2000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188943561/10000000000 : ℝ)^4623 ≤ (7103719613451/50000000000000 : ℝ)^3599 := by
    have hnat : (2188943561 : ℕ)^4623*50000000000000^3599 ≤ 7103719613451^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188943561 10000000000 7103719613451 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5466973719/10000000000 : ℝ), (4876532753/10000000000 : ℝ), (-2188943561/10000000000 : ℝ)] ![(46039420268797/100000000000000 : ℝ), (795062809959/2000000000000 : ℝ), (7103719613451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5466973719/10000000000 : ℝ)|^4623 ≤ (46039420268797/100000000000000 : ℝ)^3599
        have hw : |(5466973719/10000000000 : ℝ)|=(5466973719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4876532753/10000000000 : ℝ)|^4623 ≤ (795062809959/2000000000000 : ℝ)^3599
        have hw : |(4876532753/10000000000 : ℝ)|=(4876532753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188943561/10000000000 : ℝ)|^4623 ≤ (7103719613451/50000000000000 : ℝ)^3599
        have hw : |(-2188943561/10000000000 : ℝ)|=(2188943561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s0_3 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4131661479/10000000000 : ℝ)*x 0 + (193299303/625000000 : ℝ)*x 1 + (5437619553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4131661479/10000000000 : ℝ)^4623 ≤ (32129443557903/100000000000000 : ℝ)^3599 := by
    have hnat : (4131661479 : ℕ)^4623*100000000000000^3599 ≤ 32129443557903^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131661479 10000000000 32129443557903 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (193299303/625000000 : ℝ)^4623 ≤ (22148430523597/100000000000000 : ℝ)^3599 := by
    have hnat : (193299303 : ℕ)^4623*100000000000000^3599 ≤ 22148430523597^3599*625000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193299303 625000000 22148430523597 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437619553/10000000000 : ℝ)^4623 ≤ (5715265737729/12500000000000 : ℝ)^3599 := by
    have hnat : (5437619553 : ℕ)^4623*12500000000000^3599 ≤ 5715265737729^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437619553 10000000000 5715265737729 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4131661479/10000000000 : ℝ), (193299303/625000000 : ℝ), (5437619553/10000000000 : ℝ)] ![(32129443557903/100000000000000 : ℝ), (22148430523597/100000000000000 : ℝ), (5715265737729/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4131661479/10000000000 : ℝ)|^4623 ≤ (32129443557903/100000000000000 : ℝ)^3599
        have hw : |(4131661479/10000000000 : ℝ)|=(4131661479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(193299303/625000000 : ℝ)|^4623 ≤ (22148430523597/100000000000000 : ℝ)^3599
        have hw : |(193299303/625000000 : ℝ)|=(193299303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437619553/10000000000 : ℝ)|^4623 ≤ (5715265737729/12500000000000 : ℝ)^3599
        have hw : |(5437619553/10000000000 : ℝ)|=(5437619553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s0_4 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-163616101/1000000000 : ℝ)*x 0 + (49017263/100000000 : ℝ)*x 1 + (2924269677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163616101/1000000000 : ℝ)^4623 ≤ (9775547467863/100000000000000 : ℝ)^3599 := by
    have hnat : (163616101 : ℕ)^4623*100000000000000^3599 ≤ 9775547467863^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163616101 1000000000 9775547467863 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49017263/100000000 : ℝ)^4623 ≤ (20008572199011/50000000000000 : ℝ)^3599 := by
    have hnat : (49017263 : ℕ)^4623*50000000000000^3599 ≤ 20008572199011^3599*100000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49017263 100000000 20008572199011 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2924269677/5000000000 : ℝ)^4623 ≤ (50207308116383/100000000000000 : ℝ)^3599 := by
    have hnat : (2924269677 : ℕ)^4623*100000000000000^3599 ≤ 50207308116383^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2924269677 5000000000 50207308116383 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-163616101/1000000000 : ℝ), (49017263/100000000 : ℝ), (2924269677/5000000000 : ℝ)] ![(9775547467863/100000000000000 : ℝ), (20008572199011/50000000000000 : ℝ), (50207308116383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-163616101/1000000000 : ℝ)|^4623 ≤ (9775547467863/100000000000000 : ℝ)^3599
        have hw : |(-163616101/1000000000 : ℝ)|=(163616101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49017263/100000000 : ℝ)|^4623 ≤ (20008572199011/50000000000000 : ℝ)^3599
        have hw : |(49017263/100000000 : ℝ)|=(49017263/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2924269677/5000000000 : ℝ)|^4623 ≤ (50207308116383/100000000000000 : ℝ)^3599
        have hw : |(2924269677/5000000000 : ℝ)|=(2924269677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s0_5 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194128361/10000000000 : ℝ)*x 0 + (-608468867/5000000000 : ℝ)*x 1 + (5848541611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194128361/10000000000 : ℝ)^4623 ≤ (10777284912437/25000000000000 : ℝ)^3599 := by
    have hnat : (5194128361 : ℕ)^4623*25000000000000^3599 ≤ 10777284912437^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194128361 10000000000 10777284912437 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608468867/5000000000 : ℝ)^4623 ≤ (6683527335133/100000000000000 : ℝ)^3599 := by
    have hnat : (608468867 : ℕ)^4623*100000000000000^3599 ≤ 6683527335133^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608468867 5000000000 6683527335133 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5848541611/10000000000 : ℝ)^4623 ≤ (50207333004563/100000000000000 : ℝ)^3599 := by
    have hnat : (5848541611 : ℕ)^4623*100000000000000^3599 ≤ 50207333004563^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5848541611 10000000000 50207333004563 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194128361/10000000000 : ℝ), (-608468867/5000000000 : ℝ), (5848541611/10000000000 : ℝ)] ![(10777284912437/25000000000000 : ℝ), (6683527335133/100000000000000 : ℝ), (50207333004563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194128361/10000000000 : ℝ)|^4623 ≤ (10777284912437/25000000000000 : ℝ)^3599
        have hw : |(5194128361/10000000000 : ℝ)|=(5194128361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-608468867/5000000000 : ℝ)|^4623 ≤ (6683527335133/100000000000000 : ℝ)^3599
        have hw : |(-608468867/5000000000 : ℝ)|=(608468867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5848541611/10000000000 : ℝ)|^4623 ≤ (50207333004563/100000000000000 : ℝ)^3599
        have hw : |(5848541611/10000000000 : ℝ)|=(5848541611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s0_6 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038826263/2000000000 : ℝ)*x 0 + (5848538941/10000000000 : ℝ)*x 1 + (-1216937443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038826263/2000000000 : ℝ)^4623 ≤ (43109171142401/100000000000000 : ℝ)^3599 := by
    have hnat : (1038826263 : ℕ)^4623*100000000000000^3599 ≤ 43109171142401^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038826263 2000000000 43109171142401 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5848538941/10000000000 : ℝ)^4623 ≤ (12551825890547/25000000000000 : ℝ)^3599 := by
    have hnat : (5848538941 : ℕ)^4623*25000000000000^3599 ≤ 12551825890547^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5848538941 10000000000 12551825890547 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216937443/10000000000 : ℝ)^4623 ≤ (6683525282211/100000000000000 : ℝ)^3599 := by
    have hnat : (1216937443 : ℕ)^4623*100000000000000^3599 ≤ 6683525282211^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216937443 10000000000 6683525282211 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038826263/2000000000 : ℝ), (5848538941/10000000000 : ℝ), (-1216937443/10000000000 : ℝ)] ![(43109171142401/100000000000000 : ℝ), (12551825890547/25000000000000 : ℝ), (6683525282211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038826263/2000000000 : ℝ)|^4623 ≤ (43109171142401/100000000000000 : ℝ)^3599
        have hw : |(1038826263/2000000000 : ℝ)|=(1038826263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5848538941/10000000000 : ℝ)|^4623 ≤ (12551825890547/25000000000000 : ℝ)^3599
        have hw : |(5848538941/10000000000 : ℝ)|=(5848538941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1216937443/10000000000 : ℝ)|^4623 ≤ (6683525282211/100000000000000 : ℝ)^3599
        have hw : |(-1216937443/10000000000 : ℝ)|=(1216937443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s0_7 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4138965591/10000000000 : ℝ)*x 0 + (5378432791/10000000000 : ℝ)*x 1 + (3154069921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4138965591/10000000000 : ℝ)^4623 ≤ (6440484484669/20000000000000 : ℝ)^3599 := by
    have hnat : (4138965591 : ℕ)^4623*20000000000000^3599 ≤ 6440484484669^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138965591 10000000000 6440484484669 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5378432791/10000000000 : ℝ)^4623 ≤ (11270962130689/25000000000000 : ℝ)^3599 := by
    have hnat : (5378432791 : ℕ)^4623*25000000000000^3599 ≤ 11270962130689^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378432791 10000000000 11270962130689 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154069921/10000000000 : ℝ)^4623 ≤ (22713729033387/100000000000000 : ℝ)^3599 := by
    have hnat : (3154069921 : ℕ)^4623*100000000000000^3599 ≤ 22713729033387^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154069921 10000000000 22713729033387 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4138965591/10000000000 : ℝ), (5378432791/10000000000 : ℝ), (3154069921/10000000000 : ℝ)] ![(6440484484669/20000000000000 : ℝ), (11270962130689/25000000000000 : ℝ), (22713729033387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4138965591/10000000000 : ℝ)|^4623 ≤ (6440484484669/20000000000000 : ℝ)^3599
        have hw : |(4138965591/10000000000 : ℝ)|=(4138965591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5378432791/10000000000 : ℝ)|^4623 ≤ (11270962130689/25000000000000 : ℝ)^3599
        have hw : |(5378432791/10000000000 : ℝ)|=(5378432791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154069921/10000000000 : ℝ)|^4623 ≤ (22713729033387/100000000000000 : ℝ)^3599
        have hw : |(3154069921/10000000000 : ℝ)|=(3154069921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1563_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3461/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (621/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2/5 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2/5 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2/5 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (4621/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4621 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4621*1^1024 ≤ 0^1024*1^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4621/1024 : ℝ) ≤ (100022569159117773/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4621 ≤ (100022569159117773/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4621*6250000000000000000^1024 ≤ 100022569159117773^1024*5^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 100022569159117773 6250000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (100022569159117773/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4621 := by
      have hnat : (1 : ℕ)^1024*1^4621 ≤ 1^4621*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6350022569159117773/6250000000000000000 : ℝ) ≤ (10035244714493071/10000000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (6350022569159117773/6250000000000000000 : ℝ)^1024 ≤ (10035244714493071/10000000000000000 : ℝ)^4621 := by
      have hnat : (6350022569159117773 : ℕ)^1024*10000000000000000^4621 ≤ 10035244714493071^4621*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6350022569159117773 6250000000000000000 10035244714493071 10000000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035244714493071/10000000000000000 : ℝ)) (X := (6350022569159117773/6250000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3225022569159117773/3125000000000000000 : ℝ) ≤ (5035244714493071/5000000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (3225022569159117773/3125000000000000000 : ℝ)^1024 ≤ (5035244714493071/5000000000000000 : ℝ)^4621 := by
      have hnat : (3225022569159117773 : ℕ)^1024*5000000000000000^4621 ≤ 5035244714493071^4621*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3225022569159117773 3125000000000000000 5035244714493071 5000000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5035244714493071/5000000000000000 : ℝ)) (X := (3225022569159117773/3125000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(35244714493071/4000000000000000 : ℝ)*(0 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35244714493071/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(100022569159117773/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(35244714493071/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4621/1024 : ℝ) := by
    rw [show (1 : ℝ)+(35244714493071/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10035244714493071/10000000000000000 : ℝ) by norm_num, show 1+(100022569159117773/6250000000000000000 : ℝ)+(0 : ℝ)=(6350022569159117773/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(100022569159117773/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(35244714493071/4000000000000000 : ℝ)*(2/5 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35244714493071/4000000000000000 : ℝ)*(2/5 : ℝ)=(5035244714493071/5000000000000000 : ℝ) by norm_num, show 1+2*(100022569159117773/6250000000000000000 : ℝ)=(3225022569159117773/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(35244714493071/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35244714493071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(35244714493071/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35244714493071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(35244714493071/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35244714493071/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-326610677/2000000000 : ℝ)*X 0 0+(293731319/500000000 : ℝ)*X 0 1+(2438266403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((546697367/1000000000 : ℝ)*X 1 0+(-1094471777/5000000000 : ℝ)*X 1 1+(609566601/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5466973719/10000000000 : ℝ)*X 2 0+(4876532753/10000000000 : ℝ)*X 2 1+(-2188943561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4131661479/10000000000 : ℝ)*X 0 0+(193299303/625000000 : ℝ)*X 0 1+(5437619553/10000000000 : ℝ)*X 0 2+(4131661479/10000000000 : ℝ)*X 1 0+(193299303/625000000 : ℝ)*X 1 1+(5437619553/10000000000 : ℝ)*X 1 2+(4131661479/10000000000 : ℝ)*X 2 0+(193299303/625000000 : ℝ)*X 2 1+(5437619553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-163616101/1000000000 : ℝ)*X 0 0+(49017263/100000000 : ℝ)*X 0 1+(2924269677/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194128361/10000000000 : ℝ)*X 1 0+(-608468867/5000000000 : ℝ)*X 1 1+(5848541611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1038826263/2000000000 : ℝ)*X 2 0+(5848538941/10000000000 : ℝ)*X 2 1+(-1216937443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4138965591/10000000000 : ℝ)*X 0 0+(5378432791/10000000000 : ℝ)*X 0 1+(3154069921/10000000000 : ℝ)*X 0 2+(4138965591/10000000000 : ℝ)*X 1 0+(5378432791/10000000000 : ℝ)*X 1 1+(3154069921/10000000000 : ℝ)*X 1 2+(4138965591/10000000000 : ℝ)*X 2 0+(5378432791/10000000000 : ℝ)*X 2 1+(3154069921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5156396347100636289/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12263629/25000000000000 : ℝ)*(base1) + (535634253/50000000000000 : ℝ)*(base19) + (270062149/25000000000000 : ℝ)*(base23) + (138578067/100000000000000 : ℝ)*(upper3) + (54363/39062500000 : ℝ)*(upper5) + (714195644206757/100000000000000 : ℝ)*(major0) + (714195644206757/100000000000000 : ℝ)*(major1) + (714195644206757/100000000000000 : ℝ)*(major2) + (125239228122559/12500000000000 : ℝ)*(sp0) + (125239585200263/12500000000000 : ℝ)*(sp1) + (500958336311007/50000000000000 : ℝ)*(sp2) + (213235811456031/50000000000000 : ℝ)*(sp3) + (1988472327/50000000000000 : ℝ)*(sp4) + (1691696443/100000000000000 : ℝ)*(sp7) + (213236681831511/50000000000000 : ℝ)*(f.failure) + (100191775287061/10000000000000 : ℝ)*(f.sum) + (227274317680747/200000000000000000000000000000 : ℝ)*base65 + (1148102251719253/400000000000000000000000000000 : ℝ)*base68 + (2437410273080747/400000000000000000000000000000 : ℝ)*base69 + (328395491480747/400000000000000000000000000000 : ℝ)*base71 + (360964706719253/200000000000000000000000000000 : ℝ)*base74 + (979209760519253/400000000000000000000000000000 : ℝ)*base76 + (221303862919253/400000000000000000000000000000 : ℝ)*base78 + (1831131444519253/400000000000000000000000000000 : ℝ)*base80 + (1082299680880747/200000000000000000000000000000 : ℝ)*base81 + (383309/200000000000000000000 : ℝ)*base89 + (383309/200000000000000000000 : ℝ)*base91 + (383309/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117539159562086768414793/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (245438857/100000000000000 : ℝ)*(base19) + (922506213/100000000000000 : ℝ)*(base23) + (151025081/50000000000000 : ℝ)*(base32) + (92144071/100000000000000 : ℝ)*(base37) + (340271213/100000000000000 : ℝ)*(upper3) + (28020531/50000000000000 : ℝ)*(upper5) + (188217602961887/25000000000000 : ℝ)*(major0) + (188217602961887/25000000000000 : ℝ)*(major1) + (188217602961887/25000000000000 : ℝ)*(major2) + (1454472691/100000000000000 : ℝ)*(sp2) + (21123464159969/2000000000000 : ℝ)*(sp4) + (1056172962559593/100000000000000 : ℝ)*(sp5) + (528085415509773/50000000000000 : ℝ)*(sp6) + (44956714314297/10000000000000 : ℝ)*(sp7) + (224783768668601/50000000000000 : ℝ)*(f.failure) + (21123464159969/2000000000000 : ℝ)*(f.sum) + (117730199915023/50000000000000000000000000000 : ℝ)*base66 + (235411088415023/100000000000000000000000000000 : ℝ)*base68 + (154364671584977/100000000000000000000000000000 : ℝ)*base69 + (144179104284977/100000000000000000000000000000 : ℝ)*base71 + (233262011815023/50000000000000000000000000000 : ℝ)*base74 + (78807630715023/100000000000000000000000000000 : ℝ)*base76 + (63981729684977/100000000000000000000000000000 : ℝ)*base77 + (114856499315023/100000000000000000000000000000 : ℝ)*base80 + (101702253465023/50000000000000000000000000000 : ℝ)*base82 + (637981/200000000000000000000 : ℝ)*base90 + (637981/200000000000000000000 : ℝ)*base92 + (637981/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1563_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3461/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (621/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1563_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1563_s1_0 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1773433927/10000000000 : ℝ)*x 0 + (5538841869/10000000000 : ℝ)*x 1 + (2560934137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1773433927/10000000000 : ℝ)^4623 ≤ (10841396966377/100000000000000 : ℝ)^3599 := by
    have hnat : (1773433927 : ℕ)^4623*100000000000000^3599 ≤ 10841396966377^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773433927 10000000000 10841396966377 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5538841869/10000000000 : ℝ)^4623 ≤ (46818299788817/100000000000000 : ℝ)^3599 := by
    have hnat : (5538841869 : ℕ)^4623*100000000000000^3599 ≤ 46818299788817^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5538841869 10000000000 46818299788817 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2560934137/5000000000 : ℝ)^4623 ≤ (2646268951213/6250000000000 : ℝ)^3599 := by
    have hnat : (2560934137 : ℕ)^4623*6250000000000^3599 ≤ 2646268951213^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2560934137 5000000000 2646268951213 6250000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1773433927/10000000000 : ℝ), (5538841869/10000000000 : ℝ), (2560934137/5000000000 : ℝ)] ![(10841396966377/100000000000000 : ℝ), (46818299788817/100000000000000 : ℝ), (2646268951213/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1773433927/10000000000 : ℝ)|^4623 ≤ (10841396966377/100000000000000 : ℝ)^3599
        have hw : |(-1773433927/10000000000 : ℝ)|=(1773433927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5538841869/10000000000 : ℝ)|^4623 ≤ (46818299788817/100000000000000 : ℝ)^3599
        have hw : |(5538841869/10000000000 : ℝ)|=(5538841869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2560934137/5000000000 : ℝ)|^4623 ≤ (2646268951213/6250000000000 : ℝ)^3599
        have hw : |(2560934137/5000000000 : ℝ)|=(2560934137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s1_1 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688812803/5000000000 : ℝ)*x 0 + (-1991702379/10000000000 : ℝ)*x 1 + (5121868213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688812803/5000000000 : ℝ)^4623 ≤ (9015031499177/20000000000000 : ℝ)^3599 := by
    have hnat : (2688812803 : ℕ)^4623*20000000000000^3599 ≤ 9015031499177^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688812803 5000000000 9015031499177 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1991702379/10000000000 : ℝ)^4623 ≤ (12584539914871/100000000000000 : ℝ)^3599 := by
    have hnat : (1991702379 : ℕ)^4623*100000000000000^3599 ≤ 12584539914871^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991702379 10000000000 12584539914871 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5121868213/10000000000 : ℝ)^4623 ≤ (5292537821459/12500000000000 : ℝ)^3599 := by
    have hnat : (5121868213 : ℕ)^4623*12500000000000^3599 ≤ 5292537821459^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121868213 10000000000 5292537821459 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688812803/5000000000 : ℝ), (-1991702379/10000000000 : ℝ), (5121868213/10000000000 : ℝ)] ![(9015031499177/20000000000000 : ℝ), (12584539914871/100000000000000 : ℝ), (5292537821459/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688812803/5000000000 : ℝ)|^4623 ≤ (9015031499177/20000000000000 : ℝ)^3599
        have hw : |(2688812803/5000000000 : ℝ)|=(2688812803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1991702379/10000000000 : ℝ)|^4623 ≤ (12584539914871/100000000000000 : ℝ)^3599
        have hw : |(-1991702379/10000000000 : ℝ)|=(1991702379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5121868213/10000000000 : ℝ)|^4623 ≤ (5292537821459/12500000000000 : ℝ)^3599
        have hw : |(5121868213/10000000000 : ℝ)|=(5121868213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s1_2 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377625517/10000000000 : ℝ)*x 0 + (5121868669/10000000000 : ℝ)*x 1 + (-1991701901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377625517/10000000000 : ℝ)^4623 ≤ (9015031307527/20000000000000 : ℝ)^3599 := by
    have hnat : (5377625517 : ℕ)^4623*20000000000000^3599 ≤ 9015031307527^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377625517 10000000000 9015031307527 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5121868669/10000000000 : ℝ)^4623 ≤ (21170153706879/50000000000000 : ℝ)^3599 := by
    have hnat : (5121868669 : ℕ)^4623*50000000000000^3599 ≤ 21170153706879^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5121868669 10000000000 21170153706879 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991701901/10000000000 : ℝ)^4623 ≤ (3146134008827/25000000000000 : ℝ)^3599 := by
    have hnat : (1991701901 : ℕ)^4623*25000000000000^3599 ≤ 3146134008827^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991701901 10000000000 3146134008827 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377625517/10000000000 : ℝ), (5121868669/10000000000 : ℝ), (-1991701901/10000000000 : ℝ)] ![(9015031307527/20000000000000 : ℝ), (21170153706879/50000000000000 : ℝ), (3146134008827/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377625517/10000000000 : ℝ)|^4623 ≤ (9015031307527/20000000000000 : ℝ)^3599
        have hw : |(5377625517/10000000000 : ℝ)|=(5377625517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5121868669/10000000000 : ℝ)|^4623 ≤ (21170153706879/50000000000000 : ℝ)^3599
        have hw : |(5121868669/10000000000 : ℝ)|=(5121868669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1991701901/10000000000 : ℝ)|^4623 ≤ (3146134008827/25000000000000 : ℝ)^3599
        have hw : |(-1991701901/10000000000 : ℝ)|=(1991701901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s1_3 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2115504627/5000000000 : ℝ)*x 0 + (3764188649/10000000000 : ℝ)*x 1 + (4743789657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2115504627/5000000000 : ℝ)^4623 ≤ (33125200491559/100000000000000 : ℝ)^3599 := by
    have hnat : (2115504627 : ℕ)^4623*100000000000000^3599 ≤ 33125200491559^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115504627 5000000000 33125200491559 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3764188649/10000000000 : ℝ)^4623 ≤ (14253119626621/50000000000000 : ℝ)^3599 := by
    have hnat : (3764188649 : ℕ)^4623*50000000000000^3599 ≤ 14253119626621^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3764188649 10000000000 14253119626621 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4743789657/10000000000 : ℝ)^4623 ≤ (19184280117537/50000000000000 : ℝ)^3599 := by
    have hnat : (4743789657 : ℕ)^4623*50000000000000^3599 ≤ 19184280117537^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4743789657 10000000000 19184280117537 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2115504627/5000000000 : ℝ), (3764188649/10000000000 : ℝ), (4743789657/10000000000 : ℝ)] ![(33125200491559/100000000000000 : ℝ), (14253119626621/50000000000000 : ℝ), (19184280117537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2115504627/5000000000 : ℝ)|^4623 ≤ (33125200491559/100000000000000 : ℝ)^3599
        have hw : |(2115504627/5000000000 : ℝ)|=(2115504627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3764188649/10000000000 : ℝ)|^4623 ≤ (14253119626621/50000000000000 : ℝ)^3599
        have hw : |(3764188649/10000000000 : ℝ)|=(3764188649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4743789657/10000000000 : ℝ)|^4623 ≤ (19184280117537/50000000000000 : ℝ)^3599
        have hw : |(4743789657/10000000000 : ℝ)|=(4743789657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s1_4 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-354730859/2000000000 : ℝ)*x 0 + (16019411/31250000 : ℝ)*x 1 + (5534433883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (354730859/2000000000 : ℝ)^4623 ≤ (10843127453963/100000000000000 : ℝ)^3599 := by
    have hnat : (354730859 : ℕ)^4623*100000000000000^3599 ≤ 10843127453963^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      354730859 2000000000 10843127453963 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (16019411/31250000 : ℝ)^4623 ≤ (21193214005217/50000000000000 : ℝ)^3599 := by
    have hnat : (16019411 : ℕ)^4623*50000000000000^3599 ≤ 21193214005217^3599*31250000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16019411 31250000 21193214005217 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5534433883/10000000000 : ℝ)^4623 ≤ (23385222260907/50000000000000 : ℝ)^3599 := by
    have hnat : (5534433883 : ℕ)^4623*50000000000000^3599 ≤ 23385222260907^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5534433883 10000000000 23385222260907 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-354730859/2000000000 : ℝ), (16019411/31250000 : ℝ), (5534433883/10000000000 : ℝ)] ![(10843127453963/100000000000000 : ℝ), (21193214005217/50000000000000 : ℝ), (23385222260907/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-354730859/2000000000 : ℝ)|^4623 ≤ (10843127453963/100000000000000 : ℝ)^3599
        have hw : |(-354730859/2000000000 : ℝ)|=(354730859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(16019411/31250000 : ℝ)|^4623 ≤ (21193214005217/50000000000000 : ℝ)^3599
        have hw : |(16019411/31250000 : ℝ)|=(16019411/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5534433883/10000000000 : ℝ)|^4623 ≤ (23385222260907/50000000000000 : ℝ)^3599
        have hw : |(5534433883/10000000000 : ℝ)|=(5534433883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s1_5 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633588113/5000000000 : ℝ)*x 0 + (-1579136543/10000000000 : ℝ)*x 1 + (17295107/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633588113/5000000000 : ℝ)^4623 ≤ (43889457222333/100000000000000 : ℝ)^3599 := by
    have hnat : (2633588113 : ℕ)^4623*100000000000000^3599 ≤ 43889457222333^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633588113 5000000000 43889457222333 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1579136543/10000000000 : ℝ)^4623 ≤ (4670047178339/50000000000000 : ℝ)^3599 := by
    have hnat : (1579136543 : ℕ)^4623*50000000000000^3599 ≤ 4670047178339^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579136543 10000000000 4670047178339 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17295107/31250000 : ℝ)^4623 ≤ (46770448397143/100000000000000 : ℝ)^3599 := by
    have hnat : (17295107 : ℕ)^4623*100000000000000^3599 ≤ 46770448397143^3599*31250000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17295107 31250000 46770448397143 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633588113/5000000000 : ℝ), (-1579136543/10000000000 : ℝ), (17295107/31250000 : ℝ)] ![(43889457222333/100000000000000 : ℝ), (4670047178339/50000000000000 : ℝ), (46770448397143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633588113/5000000000 : ℝ)|^4623 ≤ (43889457222333/100000000000000 : ℝ)^3599
        have hw : |(2633588113/5000000000 : ℝ)|=(2633588113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1579136543/10000000000 : ℝ)|^4623 ≤ (4670047178339/50000000000000 : ℝ)^3599
        have hw : |(-1579136543/10000000000 : ℝ)|=(1579136543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17295107/31250000 : ℝ)|^4623 ≤ (46770448397143/100000000000000 : ℝ)^3599
        have hw : |(17295107/31250000 : ℝ)|=(17295107/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s1_6 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267175843/10000000000 : ℝ)*x 0 + (1771019/3200000 : ℝ)*x 1 + (-157913689/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267175843/10000000000 : ℝ)^4623 ≤ (21944726561453/50000000000000 : ℝ)^3599 := by
    have hnat : (5267175843 : ℕ)^4623*50000000000000^3599 ≤ 21944726561453^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267175843 10000000000 21944726561453 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1771019/3200000 : ℝ)^4623 ≤ (11692612465651/25000000000000 : ℝ)^3599 := by
    have hnat : (1771019 : ℕ)^4623*25000000000000^3599 ≤ 11692612465651^3599*3200000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1771019 3200000 11692612465651 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157913689/1000000000 : ℝ)^4623 ≤ (2335024248257/25000000000000 : ℝ)^3599 := by
    have hnat : (157913689 : ℕ)^4623*25000000000000^3599 ≤ 2335024248257^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157913689 1000000000 2335024248257 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267175843/10000000000 : ℝ), (1771019/3200000 : ℝ), (-157913689/1000000000 : ℝ)] ![(21944726561453/50000000000000 : ℝ), (11692612465651/25000000000000 : ℝ), (2335024248257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267175843/10000000000 : ℝ)|^4623 ≤ (21944726561453/50000000000000 : ℝ)^3599
        have hw : |(5267175843/10000000000 : ℝ)|=(5267175843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1771019/3200000 : ℝ)|^4623 ≤ (11692612465651/25000000000000 : ℝ)^3599
        have hw : |(1771019/3200000 : ℝ)|=(1771019/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-157913689/1000000000 : ℝ)|^4623 ≤ (2335024248257/25000000000000 : ℝ)^3599
        have hw : |(-157913689/1000000000 : ℝ)|=(157913689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s1_7 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057881461/2500000000 : ℝ)*x 0 + (473358641/1000000000 : ℝ)*x 1 + (3774544517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057881461/2500000000 : ℝ)^4623 ≤ (33130395785513/100000000000000 : ℝ)^3599 := by
    have hnat : (1057881461 : ℕ)^4623*100000000000000^3599 ≤ 33130395785513^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057881461 2500000000 33130395785513 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473358641/1000000000 : ℝ)^4623 ≤ (7652517333773/20000000000000 : ℝ)^3599 := by
    have hnat : (473358641 : ℕ)^4623*20000000000000^3599 ≤ 7652517333773^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473358641 1000000000 7652517333773 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3774544517/10000000000 : ℝ)^4623 ≤ (893969297823/3125000000000 : ℝ)^3599 := by
    have hnat : (3774544517 : ℕ)^4623*3125000000000^3599 ≤ 893969297823^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3774544517 10000000000 893969297823 3125000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057881461/2500000000 : ℝ), (473358641/1000000000 : ℝ), (3774544517/10000000000 : ℝ)] ![(33130395785513/100000000000000 : ℝ), (7652517333773/20000000000000 : ℝ), (893969297823/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057881461/2500000000 : ℝ)|^4623 ≤ (33130395785513/100000000000000 : ℝ)^3599
        have hw : |(1057881461/2500000000 : ℝ)|=(1057881461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(473358641/1000000000 : ℝ)|^4623 ≤ (7652517333773/20000000000000 : ℝ)^3599
        have hw : |(473358641/1000000000 : ℝ)|=(473358641/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3774544517/10000000000 : ℝ)|^4623 ≤ (893969297823/3125000000000 : ℝ)^3599
        have hw : |(3774544517/10000000000 : ℝ)|=(3774544517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1563_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (621/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3461/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (899/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (891/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (621/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3461/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (621/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3461/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (621/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3461/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (621/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3461/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (621/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3461/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (621/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3461/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base1 : ((1 : ℝ)*N 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 0]
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
  have hpowlo : (3461/100000 : ℝ) ^ (4621/1024 : ℝ) ≤ (25577724464461/100000000000000000000 : ℝ) := by
    have hpowers : (3461/100000 : ℝ)^4621 ≤ (25577724464461/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3461 : ℕ)^4621*100000000000000000000^1024 ≤ 25577724464461^1024*100000^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3461 100000 25577724464461 100000000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3461/100000 : ℝ)) (X := (25577724464461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (621/2500 : ℝ) ^ (4621/1024 : ℝ) ≤ (93212343416332219/50000000000000000000 : ℝ) := by
    have hpowers : (621/2500 : ℝ)^4621 ≤ (93212343416332219/50000000000000000000 : ℝ)^1024 := by
      have hnat : (621 : ℕ)^4621*50000000000000000000^1024 ≤ 93212343416332219^1024*2500^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        621 2500 93212343416332219 50000000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (621/2500 : ℝ)) (X := (93212343416332219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000025577724464461/50000000000000000000 : ℝ) ≤ (2500000283397367/2500000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (50000025577724464461/50000000000000000000 : ℝ)^1024 ≤ (2500000283397367/2500000000000000 : ℝ)^4621 := by
      have hnat : (50000025577724464461 : ℕ)^1024*2500000000000000^4621 ≤ 2500000283397367^4621*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000025577724464461 50000000000000000000 2500000283397367 2500000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000283397367/2500000000000000 : ℝ)) (X := (50000025577724464461/50000000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100186450264557128899/100000000000000000000 : ℝ) ≤ (2501032172017887/2500000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (100186450264557128899/100000000000000000000 : ℝ)^1024 ≤ (2501032172017887/2500000000000000 : ℝ)^4621 := by
      have hnat : (100186450264557128899 : ℕ)^1024*2500000000000000^4621 ≤ 2501032172017887^4621*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100186450264557128899 100000000000000000000 2501032172017887 2500000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501032172017887/2500000000000000 : ℝ)) (X := (100186450264557128899/100000000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25093212343416332219/25000000000000000000 : ℝ) ≤ (2502064060638407/2500000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (25093212343416332219/25000000000000000000 : ℝ)^1024 ≤ (2502064060638407/2500000000000000 : ℝ)^4621 := by
      have hnat : (25093212343416332219 : ℕ)^1024*2500000000000000^4621 ≤ 2502064060638407^4621*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25093212343416332219 25000000000000000000 2502064060638407 2500000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502064060638407/2500000000000000 : ℝ)) (X := (25093212343416332219/25000000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25577724464461/100000000000000000000 : ℝ) ≤ ((53440363325721069653/53447500000000000000 : ℝ)+2*(25797215513/13361875000000 : ℝ)*(3461/100000 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (53440363325721069653/53447500000000000000 : ℝ)+2*(25797215513/13361875000000 : ℝ)*(3461/100000 : ℝ)=(2500000283397367/2500000000000000 : ℝ) by norm_num, show 1+2*(25577724464461/100000000000000000000 : ℝ)=(50000025577724464461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(93212343416332219/50000000000000000000 : ℝ)+(25577724464461/100000000000000000000 : ℝ) ≤ ((53440363325721069653/53447500000000000000 : ℝ)+(25797215513/13361875000000 : ℝ)*((621/2500 : ℝ)+(3461/100000 : ℝ)))^(4621/1024 : ℝ) := by
    rw [show (53440363325721069653/53447500000000000000 : ℝ)+(25797215513/13361875000000 : ℝ)*((621/2500 : ℝ)+(3461/100000 : ℝ))=(2501032172017887/2500000000000000 : ℝ) by norm_num, show 1+(93212343416332219/50000000000000000000 : ℝ)+(25577724464461/100000000000000000000 : ℝ)=(100186450264557128899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(93212343416332219/50000000000000000000 : ℝ) ≤ ((53440363325721069653/53447500000000000000 : ℝ)+2*(25797215513/13361875000000 : ℝ)*(621/2500 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (53440363325721069653/53447500000000000000 : ℝ)+2*(25797215513/13361875000000 : ℝ)*(621/2500 : ℝ)=(2502064060638407/2500000000000000 : ℝ) by norm_num, show 1+2*(93212343416332219/50000000000000000000 : ℝ)=(25093212343416332219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53440363325721069653/53447500000000000000 : ℝ)*(X 1 0+X 2 0)+(25797215513/13361875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (3461/100000 : ℝ)) (hi := (621/2500 : ℝ)) (c := (53440363325721069653/53447500000000000000 : ℝ)) (alpha := (25797215513/13361875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53440363325721069653/53447500000000000000 : ℝ)*(X 0 1+X 2 1)+(25797215513/13361875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (3461/100000 : ℝ)) (hi := (621/2500 : ℝ)) (c := (53440363325721069653/53447500000000000000 : ℝ)) (alpha := (25797215513/13361875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53440363325721069653/53447500000000000000 : ℝ)*(X 0 2+X 1 2)+(25797215513/13361875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (3461/100000 : ℝ)) (hi := (621/2500 : ℝ)) (c := (53440363325721069653/53447500000000000000 : ℝ)) (alpha := (25797215513/13361875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1773433927/10000000000 : ℝ)*X 0 0+(5538841869/10000000000 : ℝ)*X 0 1+(2560934137/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2688812803/5000000000 : ℝ)*X 1 0+(-1991702379/10000000000 : ℝ)*X 1 1+(5121868213/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5377625517/10000000000 : ℝ)*X 2 0+(5121868669/10000000000 : ℝ)*X 2 1+(-1991701901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2115504627/5000000000 : ℝ)*X 0 0+(3764188649/10000000000 : ℝ)*X 0 1+(4743789657/10000000000 : ℝ)*X 0 2+(2115504627/5000000000 : ℝ)*X 1 0+(3764188649/10000000000 : ℝ)*X 1 1+(4743789657/10000000000 : ℝ)*X 1 2+(2115504627/5000000000 : ℝ)*X 2 0+(3764188649/10000000000 : ℝ)*X 2 1+(4743789657/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-354730859/2000000000 : ℝ)*X 0 0+(16019411/31250000 : ℝ)*X 0 1+(5534433883/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2633588113/5000000000 : ℝ)*X 1 0+(-1579136543/10000000000 : ℝ)*X 1 1+(17295107/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5267175843/10000000000 : ℝ)*X 2 0+(1771019/3200000 : ℝ)*X 2 1+(-157913689/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1057881461/2500000000 : ℝ)*X 0 0+(473358641/1000000000 : ℝ)*X 0 1+(3774544517/10000000000 : ℝ)*X 0 2+(1057881461/2500000000 : ℝ)*X 1 0+(473358641/1000000000 : ℝ)*X 1 1+(3774544517/10000000000 : ℝ)*X 1 2+(1057881461/2500000000 : ℝ)*X 2 0+(473358641/1000000000 : ℝ)*X 2 1+(3774544517/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1274965940574933231256693281/267237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6735391/6250000000000 : ℝ)*(base1) + (150895949/12500000000000 : ℝ)*(base19) + (1167476379/100000000000000 : ℝ)*(base23) + (697097/12500000000000 : ℝ)*(upper3) + (267324501/100000000000000 : ℝ)*(upper5) + (341908750671641/20000000000000 : ℝ)*(major0) + (341908750671641/20000000000000 : ℝ)*(major1) + (341908750671641/20000000000000 : ℝ)*(major2) + (2398241459746947/100000000000000 : ℝ)*(sp0) + (1199126295291687/50000000000000 : ℝ)*(sp1) + (599563157568647/25000000000000 : ℝ)*(sp2) + (1020829357464481/100000000000000 : ℝ)*(sp3) + (497830811/4000000000000 : ℝ)*(sp4) + (204235219/5000000000000 : ℝ)*(sp7) + (255208387483779/25000000000000 : ℝ)*(f.failure) + (1199126898875483/50000000000000 : ℝ)*(f.sum) + (371549941159/1068950000000000000000000000 : ℝ)*base65 + (4956803686292410573/1068950000000000000000000000000000 : ℝ)*base67 + (8371029058443810573/1068950000000000000000000000000000 : ℝ)*base69 + (6840149677829710573/1068950000000000000000000000000000 : ℝ)*base71 + (67998703730763/21379000000000000000000000000 : ℝ)*base73 + (7820516217840760573/1068950000000000000000000000000000 : ℝ)*base75 + (1874676657909310573/1068950000000000000000000000000000 : ℝ)*base77 + (1432301301737139427/1068950000000000000000000000000000 : ℝ)*base80 + (91659688228149/21379000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (798799/100000000000000000000 : ℝ)*base90 + (798799/100000000000000000000 : ℝ)*base92 + (798799/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1972069073381760976881508539/167023437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (265801827/12500000000000 : ℝ)*(base19) + (973624079/50000000000000 : ℝ)*(base23) + (2475171/25000000000000 : ℝ)*(upper2) + (170219787/50000000000000 : ℝ)*(upper3) + (227850719/100000000000000 : ℝ)*(upper5) + (109135964504373/6250000000000 : ℝ)*(major0) + (109135964504373/6250000000000 : ℝ)*(major1) + (109135964504373/6250000000000 : ℝ)*(major2) + (16884015083/100000000000000 : ℝ)*(sp1) + (7968938337/50000000000000 : ℝ)*(sp2) + (2449642753010721/100000000000000 : ℝ)*(sp4) + (1224811871290511/50000000000000 : ℝ)*(sp5) + (38275388560717/1562500000000 : ℝ)*(sp6) + (260676929389471/25000000000000 : ℝ)*(sp7) + (260676929389471/25000000000000 : ℝ)*(f.failure) + (2449642753010721/100000000000000 : ℝ)*(f.sum) + (112134181541291/21379000000000000000000000000 : ℝ)*base66 + (325091920461032431/334046875000000000000000000000000 : ℝ)*base68 + (445260418981933889/83511718750000000000000000000000 : ℝ)*base70 + (1730657617934063681/334046875000000000000000000000000 : ℝ)*base72 + (3227836974133/4275800000000000000000000000 : ℝ)*base73 + (264243694580349757/41755859375000000000000000000000 : ℝ)*base76 + (1485966869646376181/334046875000000000000000000000000 : ℝ)*base78 + (878338341106248819/334046875000000000000000000000000 : ℝ)*base79 + (1470459183899/10689500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (840549/100000000000000000000 : ℝ)*base89 + (840549/100000000000000000000 : ℝ)*base91 + (840549/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1563_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (621/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3461/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (899/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (891/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1563_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1563_s2_0 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-224083523/1250000000 : ℝ)*x 0 + (2721619631/5000000000 : ℝ)*x 1 + (260247293/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224083523/1250000000 : ℝ)^4623 ≤ (10992667920471/100000000000000 : ℝ)^3599 := by
    have hnat : (224083523 : ℕ)^4623*100000000000000^3599 ≤ 10992667920471^3599*1250000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224083523 1250000000 10992667920471 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721619631/5000000000 : ℝ)^4623 ≤ (22891416348269/50000000000000 : ℝ)^3599 := by
    have hnat : (2721619631 : ℕ)^4623*50000000000000^3599 ≤ 22891416348269^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721619631 5000000000 22891416348269 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260247293/500000000 : ℝ)^4623 ≤ (21612249682829/50000000000000 : ℝ)^3599 := by
    have hnat : (260247293 : ℕ)^4623*50000000000000^3599 ≤ 21612249682829^3599*500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260247293 500000000 21612249682829 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224083523/1250000000 : ℝ), (2721619631/5000000000 : ℝ), (260247293/500000000 : ℝ)] ![(10992667920471/100000000000000 : ℝ), (22891416348269/50000000000000 : ℝ), (21612249682829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224083523/1250000000 : ℝ)|^4623 ≤ (10992667920471/100000000000000 : ℝ)^3599
        have hw : |(-224083523/1250000000 : ℝ)|=(224083523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721619631/5000000000 : ℝ)|^4623 ≤ (22891416348269/50000000000000 : ℝ)^3599
        have hw : |(2721619631/5000000000 : ℝ)|=(2721619631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260247293/500000000 : ℝ)|^4623 ≤ (21612249682829/50000000000000 : ℝ)^3599
        have hw : |(260247293/500000000 : ℝ)|=(260247293/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s2_1 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66912227/125000000 : ℝ)*x 0 + (-383002387/2000000000 : ℝ)*x 1 + (5204946057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66912227/125000000 : ℝ)^4623 ≤ (2240497765987/5000000000000 : ℝ)^3599 := by
    have hnat : (66912227 : ℕ)^4623*5000000000000^3599 ≤ 2240497765987^3599*125000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66912227 125000000 2240497765987 5000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383002387/2000000000 : ℝ)^4623 ≤ (5982771595539/50000000000000 : ℝ)^3599 := by
    have hnat : (383002387 : ℕ)^4623*50000000000000^3599 ≤ 5982771595539^3599*2000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383002387 2000000000 5982771595539 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5204946057/10000000000 : ℝ)^4623 ≤ (43224501467123/100000000000000 : ℝ)^3599 := by
    have hnat : (5204946057 : ℕ)^4623*100000000000000^3599 ≤ 43224501467123^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204946057 10000000000 43224501467123 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66912227/125000000 : ℝ), (-383002387/2000000000 : ℝ), (5204946057/10000000000 : ℝ)] ![(2240497765987/5000000000000 : ℝ), (5982771595539/50000000000000 : ℝ), (43224501467123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66912227/125000000 : ℝ)|^4623 ≤ (2240497765987/5000000000000 : ℝ)^3599
        have hw : |(66912227/125000000 : ℝ)|=(66912227/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-383002387/2000000000 : ℝ)|^4623 ≤ (5982771595539/50000000000000 : ℝ)^3599
        have hw : |(-383002387/2000000000 : ℝ)|=(383002387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5204946057/10000000000 : ℝ)|^4623 ≤ (43224501467123/100000000000000 : ℝ)^3599
        have hw : |(5204946057/10000000000 : ℝ)|=(5204946057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s2_2 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535297847/1000000000 : ℝ)*x 0 + (5204946051/10000000000 : ℝ)*x 1 + (-1915011529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535297847/1000000000 : ℝ)^4623 ≤ (2800622415819/6250000000000 : ℝ)^3599 := by
    have hnat : (535297847 : ℕ)^4623*6250000000000^3599 ≤ 2800622415819^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535297847 1000000000 2800622415819 6250000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5204946051/10000000000 : ℝ)^4623 ≤ (43224501403119/100000000000000 : ℝ)^3599 := by
    have hnat : (5204946051 : ℕ)^4623*100000000000000^3599 ≤ 43224501403119^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204946051 10000000000 43224501403119 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1915011529/10000000000 : ℝ)^4623 ≤ (11965539932493/100000000000000 : ℝ)^3599 := by
    have hnat : (1915011529 : ℕ)^4623*100000000000000^3599 ≤ 11965539932493^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915011529 10000000000 11965539932493 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535297847/1000000000 : ℝ), (5204946051/10000000000 : ℝ), (-1915011529/10000000000 : ℝ)] ![(2800622415819/6250000000000 : ℝ), (43224501403119/100000000000000 : ℝ), (11965539932493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535297847/1000000000 : ℝ)|^4623 ≤ (2800622415819/6250000000000 : ℝ)^3599
        have hw : |(535297847/1000000000 : ℝ)|=(535297847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5204946051/10000000000 : ℝ)|^4623 ≤ (43224501403119/100000000000000 : ℝ)^3599
        have hw : |(5204946051/10000000000 : ℝ)|=(5204946051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1915011529/10000000000 : ℝ)|^4623 ≤ (11965539932493/100000000000000 : ℝ)^3599
        have hw : |(-1915011529/10000000000 : ℝ)|=(1915011529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s2_3 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244934451/10000000000 : ℝ)*x 0 + (3972533737/10000000000 : ℝ)*x 1 + (4532357673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244934451/10000000000 : ℝ)^4623 ≤ (6653061578149/20000000000000 : ℝ)^3599 := by
    have hnat : (4244934451 : ℕ)^4623*20000000000000^3599 ≤ 6653061578149^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244934451 10000000000 6653061578149 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3972533737/10000000000 : ℝ)^4623 ≤ (15274356251617/50000000000000 : ℝ)^3599 := by
    have hnat : (3972533737 : ℕ)^4623*50000000000000^3599 ≤ 15274356251617^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3972533737 10000000000 15274356251617 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532357673/10000000000 : ℝ)^4623 ≤ (36185979583269/100000000000000 : ℝ)^3599 := by
    have hnat : (4532357673 : ℕ)^4623*100000000000000^3599 ≤ 36185979583269^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532357673 10000000000 36185979583269 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244934451/10000000000 : ℝ), (3972533737/10000000000 : ℝ), (4532357673/10000000000 : ℝ)] ![(6653061578149/20000000000000 : ℝ), (15274356251617/50000000000000 : ℝ), (36185979583269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244934451/10000000000 : ℝ)|^4623 ≤ (6653061578149/20000000000000 : ℝ)^3599
        have hw : |(4244934451/10000000000 : ℝ)|=(4244934451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3972533737/10000000000 : ℝ)|^4623 ≤ (15274356251617/50000000000000 : ℝ)^3599
        have hw : |(3972533737/10000000000 : ℝ)|=(3972533737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532357673/10000000000 : ℝ)|^4623 ≤ (36185979583269/100000000000000 : ℝ)^3599
        have hw : |(4532357673/10000000000 : ℝ)|=(4532357673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s2_4 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-224088601/1250000000 : ℝ)*x 0 + (2603186381/5000000000 : ℝ)*x 1 + (5441800693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224088601/1250000000 : ℝ)^4623 ≤ (1374123488157/12500000000000 : ℝ)^3599 := by
    have hnat : (224088601 : ℕ)^4623*12500000000000^3599 ≤ 1374123488157^3599*1250000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224088601 1250000000 1374123488157 12500000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603186381/5000000000 : ℝ)^4623 ≤ (10809930299069/25000000000000 : ℝ)^3599 := by
    have hnat : (2603186381 : ℕ)^4623*25000000000000^3599 ≤ 10809930299069^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603186381 5000000000 10809930299069 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5441800693/10000000000 : ℝ)^4623 ≤ (45767290884587/100000000000000 : ℝ)^3599 := by
    have hnat : (5441800693 : ℕ)^4623*100000000000000^3599 ≤ 45767290884587^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441800693 10000000000 45767290884587 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224088601/1250000000 : ℝ), (2603186381/5000000000 : ℝ), (5441800693/10000000000 : ℝ)] ![(1374123488157/12500000000000 : ℝ), (10809930299069/25000000000000 : ℝ), (45767290884587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224088601/1250000000 : ℝ)|^4623 ≤ (1374123488157/12500000000000 : ℝ)^3599
        have hw : |(-224088601/1250000000 : ℝ)|=(224088601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603186381/5000000000 : ℝ)|^4623 ≤ (10809930299069/25000000000000 : ℝ)^3599
        have hw : |(2603186381/5000000000 : ℝ)|=(2603186381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5441800693/10000000000 : ℝ)|^4623 ≤ (45767290884587/100000000000000 : ℝ)^3599
        have hw : |(5441800693/10000000000 : ℝ)|=(5441800693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s2_5 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644989543/5000000000 : ℝ)*x 0 + (-1678157553/10000000000 : ℝ)*x 1 + (1360450339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644989543/5000000000 : ℝ)^4623 ≤ (8826735401661/20000000000000 : ℝ)^3599 := by
    have hnat : (2644989543 : ℕ)^4623*20000000000000^3599 ≤ 8826735401661^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644989543 5000000000 8826735401661 20000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1678157553/10000000000 : ℝ)^4623 ≤ (10099024928391/100000000000000 : ℝ)^3599 := by
    have hnat : (1678157553 : ℕ)^4623*100000000000000^3599 ≤ 10099024928391^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678157553 10000000000 10099024928391 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360450339/2500000000 : ℝ)^4623 ≤ (22883649023573/50000000000000 : ℝ)^3599 := by
    have hnat : (1360450339 : ℕ)^4623*50000000000000^3599 ≤ 22883649023573^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360450339 2500000000 22883649023573 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644989543/5000000000 : ℝ), (-1678157553/10000000000 : ℝ), (1360450339/2500000000 : ℝ)] ![(8826735401661/20000000000000 : ℝ), (10099024928391/100000000000000 : ℝ), (22883649023573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644989543/5000000000 : ℝ)|^4623 ≤ (8826735401661/20000000000000 : ℝ)^3599
        have hw : |(2644989543/5000000000 : ℝ)|=(2644989543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1678157553/10000000000 : ℝ)|^4623 ≤ (10099024928391/100000000000000 : ℝ)^3599
        have hw : |(-1678157553/10000000000 : ℝ)|=(1678157553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360450339/2500000000 : ℝ)|^4623 ≤ (22883649023573/50000000000000 : ℝ)^3599
        have hw : |(1360450339/2500000000 : ℝ)|=(1360450339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s2_6 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528997927/1000000000 : ℝ)*x 0 + (5441802461/10000000000 : ℝ)*x 1 + (-839077877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528997927/1000000000 : ℝ)^4623 ≤ (11033419745041/25000000000000 : ℝ)^3599 := by
    have hnat : (528997927 : ℕ)^4623*25000000000000^3599 ≤ 11033419745041^3599*1000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528997927 1000000000 11033419745041 25000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441802461/10000000000 : ℝ)^4623 ≤ (45767309984743/100000000000000 : ℝ)^3599 := by
    have hnat : (5441802461 : ℕ)^4623*100000000000000^3599 ≤ 45767309984743^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441802461 10000000000 45767309984743 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (839077877/5000000000 : ℝ)^4623 ≤ (5049505510913/50000000000000 : ℝ)^3599 := by
    have hnat : (839077877 : ℕ)^4623*50000000000000^3599 ≤ 5049505510913^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839077877 5000000000 5049505510913 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528997927/1000000000 : ℝ), (5441802461/10000000000 : ℝ), (-839077877/5000000000 : ℝ)] ![(11033419745041/25000000000000 : ℝ), (45767309984743/100000000000000 : ℝ), (5049505510913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528997927/1000000000 : ℝ)|^4623 ≤ (11033419745041/25000000000000 : ℝ)^3599
        have hw : |(528997927/1000000000 : ℝ)|=(528997927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441802461/10000000000 : ℝ)|^4623 ≤ (45767309984743/100000000000000 : ℝ)^3599
        have hw : |(5441802461/10000000000 : ℝ)|=(5441802461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-839077877/5000000000 : ℝ)|^4623 ≤ (5049505510913/50000000000000 : ℝ)^3599
        have hw : |(-839077877/5000000000 : ℝ)|=(839077877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1563_s2_7 (p : ℝ) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2122515693/5000000000 : ℝ)*x 0 + (1132251709/2500000000 : ℝ)*x 1 + (3975913099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122515693/5000000000 : ℝ)^4623 ≤ (16633141827193/50000000000000 : ℝ)^3599 := by
    have hnat : (2122515693 : ℕ)^4623*50000000000000^3599 ≤ 16633141827193^3599*5000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122515693 5000000000 16633141827193 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132251709/2500000000 : ℝ)^4623 ≤ (18075809290629/50000000000000 : ℝ)^3599 := by
    have hnat : (1132251709 : ℕ)^4623*50000000000000^3599 ≤ 18075809290629^3599*2500000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132251709 2500000000 18075809290629 50000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3975913099/10000000000 : ℝ)^4623 ≤ (30582097752597/100000000000000 : ℝ)^3599 := by
    have hnat : (3975913099 : ℕ)^4623*100000000000000^3599 ≤ 30582097752597^3599*10000000000^4623 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975913099 10000000000 30582097752597 100000000000000 4623 3599 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4623/1024 : ℝ)) 4623 3599 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122515693/5000000000 : ℝ), (1132251709/2500000000 : ℝ), (3975913099/10000000000 : ℝ)] ![(16633141827193/50000000000000 : ℝ), (18075809290629/50000000000000 : ℝ), (30582097752597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122515693/5000000000 : ℝ)|^4623 ≤ (16633141827193/50000000000000 : ℝ)^3599
        have hw : |(2122515693/5000000000 : ℝ)|=(2122515693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132251709/2500000000 : ℝ)|^4623 ≤ (18075809290629/50000000000000 : ℝ)^3599
        have hw : |(1132251709/2500000000 : ℝ)|=(1132251709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3975913099/10000000000 : ℝ)|^4623 ≤ (30582097752597/100000000000000 : ℝ)^3599
        have hw : |(3975913099/10000000000 : ℝ)|=(3975913099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1563_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (891/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (899/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (539/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15831/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (891/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (899/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (891/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (899/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (891/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (899/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (891/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (899/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (891/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (899/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (891/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (899/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (899/10000 : ℝ) ^ (4621/1024 : ℝ) ≤ (1899486735503723/100000000000000000000 : ℝ) := by
    have hpowers : (899/10000 : ℝ)^4621 ≤ (1899486735503723/100000000000000000000 : ℝ)^1024 := by
      have hnat : (899 : ℕ)^4621*100000000000000000000^1024 ≤ 1899486735503723^1024*10000^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        899 10000 1899486735503723 100000000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (899/10000 : ℝ)) (X := (1899486735503723/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (891/5000 : ℝ) ^ (4621/1024 : ℝ) ≤ (41646133582123659/100000000000000000000 : ℝ) := by
    have hpowers : (891/5000 : ℝ)^4621 ≤ (41646133582123659/100000000000000000000 : ℝ)^1024 := by
      have hnat : (891 : ℕ)^4621*100000000000000000000^1024 ≤ 41646133582123659^1024*5000^4621 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        891 5000 41646133582123659 100000000000000000000 4621 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (891/5000 : ℝ)) (X := (41646133582123659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001899486735503723/50000000000000000000 : ℝ) ≤ (10000084182889357/10000000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (50001899486735503723/50000000000000000000 : ℝ)^1024 ≤ (10000084182889357/10000000000000000 : ℝ)^4621 := by
      have hnat : (50001899486735503723 : ℕ)^1024*10000000000000000^4621 ≤ 10000084182889357^4621*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001899486735503723 50000000000000000000 10000084182889357 10000000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084182889357/10000000000000000 : ℝ)) (X := (50001899486735503723/50000000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021772810158813691/50000000000000000000 : ℝ) ≤ (100009647946313/100000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (50021772810158813691/50000000000000000000 : ℝ)^1024 ≤ (100009647946313/100000000000000 : ℝ)^4621 := by
      have hnat : (50021772810158813691 : ℕ)^1024*100000000000000^4621 ≤ 100009647946313^4621*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021772810158813691 50000000000000000000 100009647946313 100000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100009647946313/100000000000000 : ℝ)) (X := (50021772810158813691/50000000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50041646133582123659/50000000000000000000 : ℝ) ≤ (10001845406373243/10000000000000000 : ℝ) ^ (4621/1024 : ℝ) := by
    have hpowers : (50041646133582123659/50000000000000000000 : ℝ)^1024 ≤ (10001845406373243/10000000000000000 : ℝ)^4621 := by
      have hnat : (50041646133582123659 : ℕ)^1024*10000000000000000^4621 ≤ 10001845406373243^4621*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50041646133582123659 50000000000000000000 10001845406373243 10000000000000000 1024 4621 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001845406373243/10000000000000000 : ℝ)) (X := (50041646133582123659/50000000000000000000 : ℝ)) (by norm_num) 4621 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1899486735503723/100000000000000000000 : ℝ) ≤ ((8828490993579288717/8830000000000000000 : ℝ)+2*(880611741943/883000000000000 : ℝ)*(899/10000 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (8828490993579288717/8830000000000000000 : ℝ)+2*(880611741943/883000000000000 : ℝ)*(899/10000 : ℝ)=(10000084182889357/10000000000000000 : ℝ) by norm_num, show 1+2*(1899486735503723/100000000000000000000 : ℝ)=(50001899486735503723/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41646133582123659/100000000000000000000 : ℝ)+(1899486735503723/100000000000000000000 : ℝ) ≤ ((8828490993579288717/8830000000000000000 : ℝ)+(880611741943/883000000000000 : ℝ)*((891/5000 : ℝ)+(899/10000 : ℝ)))^(4621/1024 : ℝ) := by
    rw [show (8828490993579288717/8830000000000000000 : ℝ)+(880611741943/883000000000000 : ℝ)*((891/5000 : ℝ)+(899/10000 : ℝ))=(100009647946313/100000000000000 : ℝ) by norm_num, show 1+(41646133582123659/100000000000000000000 : ℝ)+(1899486735503723/100000000000000000000 : ℝ)=(50021772810158813691/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41646133582123659/100000000000000000000 : ℝ) ≤ ((8828490993579288717/8830000000000000000 : ℝ)+2*(880611741943/883000000000000 : ℝ)*(891/5000 : ℝ))^(4621/1024 : ℝ) := by
    rw [show (8828490993579288717/8830000000000000000 : ℝ)+2*(880611741943/883000000000000 : ℝ)*(891/5000 : ℝ)=(10001845406373243/10000000000000000 : ℝ) by norm_num, show 1+2*(41646133582123659/100000000000000000000 : ℝ)=(50041646133582123659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8828490993579288717/8830000000000000000 : ℝ)*(X 1 0+X 2 0)+(880611741943/883000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (899/10000 : ℝ)) (hi := (891/5000 : ℝ)) (c := (8828490993579288717/8830000000000000000 : ℝ)) (alpha := (880611741943/883000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8828490993579288717/8830000000000000000 : ℝ)*(X 0 1+X 2 1)+(880611741943/883000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (899/10000 : ℝ)) (hi := (891/5000 : ℝ)) (c := (8828490993579288717/8830000000000000000 : ℝ)) (alpha := (880611741943/883000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8828490993579288717/8830000000000000000 : ℝ)*(X 0 2+X 1 2)+(880611741943/883000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4621/1024 : ℝ)) (lo := (899/10000 : ℝ)) (hi := (891/5000 : ℝ)) (c := (8828490993579288717/8830000000000000000 : ℝ)) (alpha := (880611741943/883000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-224083523/1250000000 : ℝ)*X 0 0+(2721619631/5000000000 : ℝ)*X 0 1+(260247293/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66912227/125000000 : ℝ)*X 1 0+(-383002387/2000000000 : ℝ)*X 1 1+(5204946057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535297847/1000000000 : ℝ)*X 2 0+(5204946051/10000000000 : ℝ)*X 2 1+(-1915011529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4244934451/10000000000 : ℝ)*X 0 0+(3972533737/10000000000 : ℝ)*X 0 1+(4532357673/10000000000 : ℝ)*X 0 2+(4244934451/10000000000 : ℝ)*X 1 0+(3972533737/10000000000 : ℝ)*X 1 1+(4532357673/10000000000 : ℝ)*X 1 2+(4244934451/10000000000 : ℝ)*X 2 0+(3972533737/10000000000 : ℝ)*X 2 1+(4532357673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-224088601/1250000000 : ℝ)*X 0 0+(2603186381/5000000000 : ℝ)*X 0 1+(5441800693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644989543/5000000000 : ℝ)*X 1 0+(-1678157553/10000000000 : ℝ)*X 1 1+(1360450339/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528997927/1000000000 : ℝ)*X 2 0+(5441802461/10000000000 : ℝ)*X 2 1+(-839077877/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2122515693/5000000000 : ℝ)*X 0 0+(1132251709/2500000000 : ℝ)*X 0 1+(3975913099/10000000000 : ℝ)*X 0 2+(2122515693/5000000000 : ℝ)*X 1 0+(1132251709/2500000000 : ℝ)*X 1 1+(3975913099/10000000000 : ℝ)*X 1 2+(2122515693/5000000000 : ℝ)*X 2 0+(1132251709/2500000000 : ℝ)*X 2 1+(3975913099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1563_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (375986498482156803805440639/110375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (187648259/50000000000000 : ℝ)*(base19) + (556179653/100000000000000 : ℝ)*(base23) + (60045003/100000000000000 : ℝ)*(upper4) + (119951761/100000000000000 : ℝ)*(upper5) + (747851926817237/25000000000000 : ℝ)*(major0) + (747851926817237/25000000000000 : ℝ)*(major1) + (747851926817237/25000000000000 : ℝ)*(major2) + (839303345079131/20000000000000 : ℝ)*(sp0) + (4196527438265767/100000000000000 : ℝ)*(sp1) + (16392701203359/390625000000 : ℝ)*(sp2) + (357255936374831/20000000000000 : ℝ)*(sp3) + (7669421951/50000000000000 : ℝ)*(sp4) + (531334659/12500000000000 : ℝ)*(sp5) + (888718989/25000000000000 : ℝ)*(sp7) + (178628323675011/10000000000000 : ℝ)*(f.failure) + (2098266032119779/50000000000000 : ℝ)*(f.sum) + (69961429795893/22075000000000000000000000000 : ℝ)*base66 + (3196828024341374929/220750000000000000000000000000000 : ℝ)*base67 + (3166111774421374929/220750000000000000000000000000000 : ℝ)*base69 + (1232099018295374929/220750000000000000000000000000000 : ℝ)*base71 + (5645762648673/1379687500000000000000000000 : ℝ)*base74 + (5268523921247624929/220750000000000000000000000000000 : ℝ)*base75 + (1598525305759374929/220750000000000000000000000000000 : ℝ)*base77 + (3577967210563874929/220750000000000000000000000000000 : ℝ)*base79 + (13727931483743/22075000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (690191/40000000000000000000 : ℝ)*base90 + (690191/40000000000000000000 : ℝ)*base92 + (690191/40000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1628534157595731279542847831/110375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14576473/100000000000000 : ℝ)*(base19) + (1194153273/100000000000000 : ℝ)*(base23) + (102760821/50000000000000 : ℝ)*(upper3) + (277414829/100000000000000 : ℝ)*(lower4) + (57626601/50000000000000 : ℝ)*(upper5) + (1513898423585319/50000000000000 : ℝ)*(major0) + (1513898423585319/50000000000000 : ℝ)*(major1) + (1513898423585319/50000000000000 : ℝ)*(major2) + (3493153851/100000000000000 : ℝ)*(sp1) + (46100571951/100000000000000 : ℝ)*(sp2) + (212379031364577/5000000000000 : ℝ)*(sp4) + (8296049061643/195312500000 : ℝ)*(sp5) + (1061883333141579/25000000000000 : ℝ)*(sp6) + (904006287615593/50000000000000 : ℝ)*(sp7) + (904006287615593/50000000000000 : ℝ)*(f.failure) + (212379031364577/5000000000000 : ℝ)*(f.sum) + (18701883902117/22075000000000000000000000000 : ℝ)*base65 + (3896875181427715723/441500000000000000000000000000000 : ℝ)*base67 + (713851330579284277/441500000000000000000000000000000 : ℝ)*base70 + (3227470428453715723/441500000000000000000000000000000 : ℝ)*base71 + (1572023624787/1379687500000000000000000000 : ℝ)*base73 + (1261601928126215723/441500000000000000000000000000000 : ℝ)*base75 + (4168067832362715723/441500000000000000000000000000000 : ℝ)*base77 + (5060543046202215723/441500000000000000000000000000000 : ℝ)*base79 + (23445764433127/5518750000000000000000000000 : ℝ)*base82 + (33933/200000000000000000000 : ℝ)*base90 + (33933/200000000000000000000 : ℝ)*base92 + (33933/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1563_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (891/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (899/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15831/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1563_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1563_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15831/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1563_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1563_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1563_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4621/1024 : ℝ) ≤ p) (hpb : p ≤ (4623/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (6698619/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (539/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15831/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1563_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
