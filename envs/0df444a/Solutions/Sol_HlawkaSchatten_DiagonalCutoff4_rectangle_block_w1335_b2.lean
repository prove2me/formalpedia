-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1335_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:46.351994+00:00
-- url     : https://prove2.me/submissions/4e8efcef-e9c7-4f1f-b127-fc02957c0c0b

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
theorem support_rectangle_w1335_s6_0 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2050030193/10000000000 : ℝ)*x 0 + (5413083011/10000000000 : ℝ)*x 1 + (5244377969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2050030193/10000000000 : ℝ)^4295 ≤ (3120642254721/25000000000000 : ℝ)^3271 := by
    have hnat : (2050030193 : ℕ)^4295*25000000000000^3271 ≤ 3120642254721^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050030193 10000000000 3120642254721 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413083011/10000000000 : ℝ)^4295 ≤ (44668199837531/100000000000000 : ℝ)^3271 := by
    have hnat : (5413083011 : ℕ)^4295*100000000000000^3271 ≤ 44668199837531^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413083011 10000000000 44668199837531 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244377969/10000000000 : ℝ)^4295 ≤ (21424615564161/50000000000000 : ℝ)^3271 := by
    have hnat : (5244377969 : ℕ)^4295*50000000000000^3271 ≤ 21424615564161^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244377969 10000000000 21424615564161 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2050030193/10000000000 : ℝ), (5413083011/10000000000 : ℝ), (5244377969/10000000000 : ℝ)] ![(3120642254721/25000000000000 : ℝ), (44668199837531/100000000000000 : ℝ), (21424615564161/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2050030193/10000000000 : ℝ)|^4295 ≤ (3120642254721/25000000000000 : ℝ)^3271
        have hw : |(-2050030193/10000000000 : ℝ)|=(2050030193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413083011/10000000000 : ℝ)|^4295 ≤ (44668199837531/100000000000000 : ℝ)^3271
        have hw : |(5413083011/10000000000 : ℝ)|=(5413083011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244377969/10000000000 : ℝ)|^4295 ≤ (21424615564161/50000000000000 : ℝ)^3271
        have hw : |(5244377969/10000000000 : ℝ)|=(5244377969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s6_1 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337280383/2500000000 : ℝ)*x 0 + (-2135992473/10000000000 : ℝ)*x 1 + (1311094491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337280383/2500000000 : ℝ)^4295 ≤ (10994112642191/25000000000000 : ℝ)^3271 := by
    have hnat : (1337280383 : ℕ)^4295*25000000000000^3271 ≤ 10994112642191^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337280383 2500000000 10994112642191 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2135992473/10000000000 : ℝ)^4295 ≤ (2634863665941/20000000000000 : ℝ)^3271 := by
    have hnat : (2135992473 : ℕ)^4295*20000000000000^3271 ≤ 2634863665941^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135992473 10000000000 2634863665941 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311094491/2500000000 : ℝ)^4295 ≤ (1071230776867/2500000000000 : ℝ)^3271 := by
    have hnat : (1311094491 : ℕ)^4295*2500000000000^3271 ≤ 1071230776867^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311094491 2500000000 1071230776867 2500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337280383/2500000000 : ℝ), (-2135992473/10000000000 : ℝ), (1311094491/2500000000 : ℝ)] ![(10994112642191/25000000000000 : ℝ), (2634863665941/20000000000000 : ℝ), (1071230776867/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337280383/2500000000 : ℝ)|^4295 ≤ (10994112642191/25000000000000 : ℝ)^3271
        have hw : |(1337280383/2500000000 : ℝ)|=(1337280383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2135992473/10000000000 : ℝ)|^4295 ≤ (2634863665941/20000000000000 : ℝ)^3271
        have hw : |(-2135992473/10000000000 : ℝ)|=(2135992473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311094491/2500000000 : ℝ)|^4295 ≤ (1071230776867/2500000000000 : ℝ)^3271
        have hw : |(1311094491/2500000000 : ℝ)|=(1311094491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s6_2 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534912149/1000000000 : ℝ)*x 0 + (1311094501/2500000000 : ℝ)*x 1 + (-2135992477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534912149/1000000000 : ℝ)^4295 ≤ (2748528132211/6250000000000 : ℝ)^3271 := by
    have hnat : (534912149 : ℕ)^4295*6250000000000^3271 ≤ 2748528132211^3271*1000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534912149 1000000000 2748528132211 6250000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311094501/2500000000 : ℝ)^4295 ≤ (42849231503813/100000000000000 : ℝ)^3271 := by
    have hnat : (1311094501 : ℕ)^4295*100000000000000^3271 ≤ 42849231503813^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311094501 2500000000 42849231503813 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135992477/10000000000 : ℝ)^4295 ≤ (13174318362099/100000000000000 : ℝ)^3271 := by
    have hnat : (2135992477 : ℕ)^4295*100000000000000^3271 ≤ 13174318362099^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135992477 10000000000 13174318362099 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534912149/1000000000 : ℝ), (1311094501/2500000000 : ℝ), (-2135992477/10000000000 : ℝ)] ![(2748528132211/6250000000000 : ℝ), (42849231503813/100000000000000 : ℝ), (13174318362099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534912149/1000000000 : ℝ)|^4295 ≤ (2748528132211/6250000000000 : ℝ)^3271
        have hw : |(534912149/1000000000 : ℝ)|=(534912149/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311094501/2500000000 : ℝ)|^4295 ≤ (42849231503813/100000000000000 : ℝ)^3271
        have hw : |(1311094501/2500000000 : ℝ)|=(1311094501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135992477/10000000000 : ℝ)|^4295 ≤ (13174318362099/100000000000000 : ℝ)^3271
        have hw : |(-2135992477/10000000000 : ℝ)|=(2135992477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s6_3 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (173138049/400000000 : ℝ)*x 0 + (2077798429/5000000000 : ℝ)*x 1 + (563503933/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173138049/400000000 : ℝ)^4295 ≤ (16651560319717/50000000000000 : ℝ)^3271 := by
    have hnat : (173138049 : ℕ)^4295*50000000000000^3271 ≤ 16651560319717^3271*400000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173138049 400000000 16651560319717 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077798429/5000000000 : ℝ)^4295 ≤ (98649537057/312500000000 : ℝ)^3271 := by
    have hnat : (2077798429 : ℕ)^4295*312500000000^3271 ≤ 98649537057^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077798429 5000000000 98649537057 312500000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (563503933/1250000000 : ℝ)^4295 ≤ (17564513742383/50000000000000 : ℝ)^3271 := by
    have hnat : (563503933 : ℕ)^4295*50000000000000^3271 ≤ 17564513742383^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563503933 1250000000 17564513742383 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173138049/400000000 : ℝ), (2077798429/5000000000 : ℝ), (563503933/1250000000 : ℝ)] ![(16651560319717/50000000000000 : ℝ), (98649537057/312500000000 : ℝ), (17564513742383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173138049/400000000 : ℝ)|^4295 ≤ (16651560319717/50000000000000 : ℝ)^3271
        have hw : |(173138049/400000000 : ℝ)|=(173138049/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077798429/5000000000 : ℝ)|^4295 ≤ (98649537057/312500000000 : ℝ)^3271
        have hw : |(2077798429/5000000000 : ℝ)|=(2077798429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(563503933/1250000000 : ℝ)|^4295 ≤ (17564513742383/50000000000000 : ℝ)^3271
        have hw : |(563503933/1250000000 : ℝ)|=(563503933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s6_4 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1025021319/5000000000 : ℝ)*x 0 + (524498157/1000000000 : ℝ)*x 1 + (5412476159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1025021319/5000000000 : ℝ)^4295 ≤ (6241334259279/50000000000000 : ℝ)^3271 := by
    have hnat : (1025021319 : ℕ)^4295*50000000000000^3271 ≤ 6241334259279^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025021319 5000000000 6241334259279 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524498157/1000000000 : ℝ)^4295 ≤ (21427853434489/50000000000000 : ℝ)^3271 := by
    have hnat : (524498157 : ℕ)^4295*50000000000000^3271 ≤ 21427853434489^3271*1000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524498157 1000000000 21427853434489 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412476159/10000000000 : ℝ)^4295 ≤ (5582703074797/12500000000000 : ℝ)^3271 := by
    have hnat : (5412476159 : ℕ)^4295*12500000000000^3271 ≤ 5582703074797^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412476159 10000000000 5582703074797 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1025021319/5000000000 : ℝ), (524498157/1000000000 : ℝ), (5412476159/10000000000 : ℝ)] ![(6241334259279/50000000000000 : ℝ), (21427853434489/50000000000000 : ℝ), (5582703074797/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1025021319/5000000000 : ℝ)|^4295 ≤ (6241334259279/50000000000000 : ℝ)^3271
        have hw : |(-1025021319/5000000000 : ℝ)|=(1025021319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524498157/1000000000 : ℝ)|^4295 ≤ (21427853434489/50000000000000 : ℝ)^3271
        have hw : |(524498157/1000000000 : ℝ)|=(524498157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412476159/10000000000 : ℝ)|^4295 ≤ (5582703074797/12500000000000 : ℝ)^3271
        have hw : |(5412476159/10000000000 : ℝ)|=(5412476159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s6_5 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305701829/10000000000 : ℝ)*x 0 + (-983947103/5000000000 : ℝ)*x 1 + (5412476593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305701829/10000000000 : ℝ)^4295 ≤ (43508334009517/100000000000000 : ℝ)^3271 := by
    have hnat : (5305701829 : ℕ)^4295*100000000000000^3271 ≤ 43508334009517^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305701829 10000000000 43508334009517 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983947103/5000000000 : ℝ)^4295 ≤ (11830036673989/100000000000000 : ℝ)^3271 := by
    have hnat : (983947103 : ℕ)^4295*100000000000000^3271 ≤ 11830036673989^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983947103 5000000000 11830036673989 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412476593/10000000000 : ℝ)^4295 ≤ (22330814650341/50000000000000 : ℝ)^3271 := by
    have hnat : (5412476593 : ℕ)^4295*50000000000000^3271 ≤ 22330814650341^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412476593 10000000000 22330814650341 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305701829/10000000000 : ℝ), (-983947103/5000000000 : ℝ), (5412476593/10000000000 : ℝ)] ![(43508334009517/100000000000000 : ℝ), (11830036673989/100000000000000 : ℝ), (22330814650341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305701829/10000000000 : ℝ)|^4295 ≤ (43508334009517/100000000000000 : ℝ)^3271
        have hw : |(5305701829/10000000000 : ℝ)|=(5305701829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983947103/5000000000 : ℝ)|^4295 ≤ (11830036673989/100000000000000 : ℝ)^3271
        have hw : |(-983947103/5000000000 : ℝ)|=(983947103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412476593/10000000000 : ℝ)|^4295 ≤ (22330814650341/50000000000000 : ℝ)^3271
        have hw : |(5412476593/10000000000 : ℝ)|=(5412476593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s6_6 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305702319/10000000000 : ℝ)*x 0 + (2706237991/5000000000 : ℝ)*x 1 + (-245986797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305702319/10000000000 : ℝ)^4295 ≤ (1087708482139/2500000000000 : ℝ)^3271 := by
    have hnat : (5305702319 : ℕ)^4295*2500000000000^3271 ≤ 1087708482139^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305702319 10000000000 1087708482139 2500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706237991/5000000000 : ℝ)^4295 ≤ (5582702835077/12500000000000 : ℝ)^3271 := by
    have hnat : (2706237991 : ℕ)^4295*12500000000000^3271 ≤ 5582702835077^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706237991 5000000000 5582702835077 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245986797/1250000000 : ℝ)^4295 ≤ (94640304127/800000000000 : ℝ)^3271 := by
    have hnat : (245986797 : ℕ)^4295*800000000000^3271 ≤ 94640304127^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245986797 1250000000 94640304127 800000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305702319/10000000000 : ℝ), (2706237991/5000000000 : ℝ), (-245986797/1250000000 : ℝ)] ![(1087708482139/2500000000000 : ℝ), (5582702835077/12500000000000 : ℝ), (94640304127/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305702319/10000000000 : ℝ)|^4295 ≤ (1087708482139/2500000000000 : ℝ)^3271
        have hw : |(5305702319/10000000000 : ℝ)|=(5305702319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706237991/5000000000 : ℝ)|^4295 ≤ (5582702835077/12500000000000 : ℝ)^3271
        have hw : |(2706237991/5000000000 : ℝ)|=(2706237991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245986797/1250000000 : ℝ)|^4295 ≤ (94640304127/800000000000 : ℝ)^3271
        have hw : |(-245986797/1250000000 : ℝ)|=(245986797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s6_7 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328476961/10000000000 : ℝ)*x 0 + (2253384843/5000000000 : ℝ)*x 1 + (4156865021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328476961/10000000000 : ℝ)^4295 ≤ (8325845160327/25000000000000 : ℝ)^3271 := by
    have hnat : (4328476961 : ℕ)^4295*25000000000000^3271 ≤ 8325845160327^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328476961 10000000000 8325845160327 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253384843/5000000000 : ℝ)^4295 ≤ (7023223499971/20000000000000 : ℝ)^3271 := by
    have hnat : (2253384843 : ℕ)^4295*20000000000000^3271 ≤ 7023223499971^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253384843 5000000000 7023223499971 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156865021/10000000000 : ℝ)^4295 ≤ (31580501844851/100000000000000 : ℝ)^3271 := by
    have hnat : (4156865021 : ℕ)^4295*100000000000000^3271 ≤ 31580501844851^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156865021 10000000000 31580501844851 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328476961/10000000000 : ℝ), (2253384843/5000000000 : ℝ), (4156865021/10000000000 : ℝ)] ![(8325845160327/25000000000000 : ℝ), (7023223499971/20000000000000 : ℝ), (31580501844851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328476961/10000000000 : ℝ)|^4295 ≤ (8325845160327/25000000000000 : ℝ)^3271
        have hw : |(4328476961/10000000000 : ℝ)|=(4328476961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253384843/5000000000 : ℝ)|^4295 ≤ (7023223499971/20000000000000 : ℝ)^3271
        have hw : |(2253384843/5000000000 : ℝ)|=(2253384843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156865021/10000000000 : ℝ)|^4295 ≤ (31580501844851/100000000000000 : ℝ)^3271
        have hw : |(4156865021/10000000000 : ℝ)|=(4156865021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1335_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2783/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14703/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2781/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2781/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2781/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2781/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2781/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2781/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2781/25000 : ℝ) ^ (2147/512 : ℝ) ≤ (2503626551297969/25000000000000000000 : ℝ) := by
    have hpowers : (2781/25000 : ℝ)^2147 ≤ (2503626551297969/25000000000000000000 : ℝ)^512 := by
      have hnat : (2781 : ℕ)^2147*25000000000000000000^512 ≤ 2503626551297969^512*25000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2781 25000 2503626551297969 25000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2781/25000 : ℝ)) (X := (2503626551297969/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14711/100000 : ℝ) ^ (2147/512 : ℝ) ≤ (8082851608479803/25000000000000000000 : ℝ) := by
    have hpowers : (14711/100000 : ℝ)^2147 ≤ (8082851608479803/25000000000000000000 : ℝ)^512 := by
      have hnat : (14711 : ℕ)^2147*25000000000000000000^512 ≤ 8082851608479803^512*100000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14711 100000 8082851608479803 25000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14711/100000 : ℝ)) (X := (8082851608479803/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502503626551297969/12500000000000000000 : ℝ) ≤ (10000477600017591/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (12502503626551297969/12500000000000000000 : ℝ)^512 ≤ (10000477600017591/10000000000000000 : ℝ)^2147 := by
      have hnat : (12502503626551297969 : ℕ)^512*10000000000000000^2147 ≤ 10000477600017591^2147*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502503626551297969 12500000000000000000 10000477600017591 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000477600017591/10000000000000000 : ℝ)) (X := (12502503626551297969/12500000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252646619539944443/6250000000000000000 : ℝ) ≤ (2500252417469997/2500000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (6252646619539944443/6250000000000000000 : ℝ)^512 ≤ (2500252417469997/2500000000000000 : ℝ)^2147 := by
      have hnat : (6252646619539944443 : ℕ)^512*2500000000000000^2147 ≤ 2500252417469997^2147*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252646619539944443 6250000000000000000 2500252417469997 2500000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500252417469997/2500000000000000 : ℝ)) (X := (6252646619539944443/6250000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508082851608479803/12500000000000000000 : ℝ) ≤ (2000308347948477/2000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (12508082851608479803/12500000000000000000 : ℝ)^512 ≤ (2000308347948477/2000000000000000 : ℝ)^2147 := by
      have hnat : (12508082851608479803 : ℕ)^512*2000000000000000^2147 ≤ 2000308347948477^2147*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508082851608479803 12500000000000000000 2000308347948477 2000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000308347948477/2000000000000000 : ℝ)) (X := (12508082851608479803/12500000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2503626551297969/25000000000000000000 : ℝ) ≤ ((35859875660964490461/35870000000000000000 : ℝ)+2*(532069862397/358700000000000 : ℝ)*(2781/25000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (35859875660964490461/35870000000000000000 : ℝ)+2*(532069862397/358700000000000 : ℝ)*(2781/25000 : ℝ)=(10000477600017591/10000000000000000 : ℝ) by norm_num, show 1+2*(2503626551297969/25000000000000000000 : ℝ)=(12502503626551297969/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8082851608479803/25000000000000000000 : ℝ)+(2503626551297969/25000000000000000000 : ℝ) ≤ ((35859875660964490461/35870000000000000000 : ℝ)+(532069862397/358700000000000 : ℝ)*((14711/100000 : ℝ)+(2781/25000 : ℝ)))^(2147/512 : ℝ) := by
    rw [show (35859875660964490461/35870000000000000000 : ℝ)+(532069862397/358700000000000 : ℝ)*((14711/100000 : ℝ)+(2781/25000 : ℝ))=(2500252417469997/2500000000000000 : ℝ) by norm_num, show 1+(8082851608479803/25000000000000000000 : ℝ)+(2503626551297969/25000000000000000000 : ℝ)=(6252646619539944443/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8082851608479803/25000000000000000000 : ℝ) ≤ ((35859875660964490461/35870000000000000000 : ℝ)+2*(532069862397/358700000000000 : ℝ)*(14711/100000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (35859875660964490461/35870000000000000000 : ℝ)+2*(532069862397/358700000000000 : ℝ)*(14711/100000 : ℝ)=(2000308347948477/2000000000000000 : ℝ) by norm_num, show 1+2*(8082851608479803/25000000000000000000 : ℝ)=(12508082851608479803/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35859875660964490461/35870000000000000000 : ℝ)*(X 1 0+X 2 0)+(532069862397/358700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (35859875660964490461/35870000000000000000 : ℝ)) (alpha := (532069862397/358700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35859875660964490461/35870000000000000000 : ℝ)*(X 0 1+X 2 1)+(532069862397/358700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (35859875660964490461/35870000000000000000 : ℝ)) (alpha := (532069862397/358700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35859875660964490461/35870000000000000000 : ℝ)*(X 0 2+X 1 2)+(532069862397/358700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (2781/25000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (35859875660964490461/35870000000000000000 : ℝ)) (alpha := (532069862397/358700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2050030193/10000000000 : ℝ)*X 0 0+(5413083011/10000000000 : ℝ)*X 0 1+(5244377969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337280383/2500000000 : ℝ)*X 1 0+(-2135992473/10000000000 : ℝ)*X 1 1+(1311094491/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534912149/1000000000 : ℝ)*X 2 0+(1311094501/2500000000 : ℝ)*X 2 1+(-2135992477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((173138049/400000000 : ℝ)*X 0 0+(2077798429/5000000000 : ℝ)*X 0 1+(563503933/1250000000 : ℝ)*X 0 2+(173138049/400000000 : ℝ)*X 1 0+(2077798429/5000000000 : ℝ)*X 1 1+(563503933/1250000000 : ℝ)*X 1 2+(173138049/400000000 : ℝ)*X 2 0+(2077798429/5000000000 : ℝ)*X 2 1+(563503933/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1025021319/5000000000 : ℝ)*X 0 0+(524498157/1000000000 : ℝ)*X 0 1+(5412476159/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305701829/10000000000 : ℝ)*X 1 0+(-983947103/5000000000 : ℝ)*X 1 1+(5412476593/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305702319/10000000000 : ℝ)*X 2 0+(2706237991/5000000000 : ℝ)*X 2 1+(-245986797/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328476961/10000000000 : ℝ)*X 0 0+(2253384843/5000000000 : ℝ)*X 0 1+(4156865021/10000000000 : ℝ)*X 0 2+(4328476961/10000000000 : ℝ)*X 1 0+(2253384843/5000000000 : ℝ)*X 1 1+(4156865021/10000000000 : ℝ)*X 1 2+(4328476961/10000000000 : ℝ)*X 2 0+(2253384843/5000000000 : ℝ)*X 2 1+(4156865021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1015728869863472628303580437/179350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1083130139/100000000000000 : ℝ)*(base19) + (991950751/100000000000000 : ℝ)*(base23) + (4775451/20000000000000 : ℝ)*(lower2) + (71812609/50000000000000 : ℝ)*(upper3) + (98083547/100000000000000 : ℝ)*(upper5) + (438248950928513/10000000000000 : ℝ)*(major0) + (438248950928513/10000000000000 : ℝ)*(major1) + (438248950928513/10000000000000 : ℝ)*(major2) + (5927528418145247/100000000000000 : ℝ)*(sp0) + (5927549257128737/100000000000000 : ℝ)*(sp1) + (1481887337077031/25000000000000 : ℝ)*(sp2) + (1418708386692949/50000000000000 : ℝ)*(sp3) + (21922113629/100000000000000 : ℝ)*(sp4) + (2343229167/20000000000000 : ℝ)*(sp7) + (709357122382933/25000000000000 : ℝ)*(f.failure) + (47420402722071/800000000000 : ℝ)*(f.sum) + (5406944898611/1793500000000000000000000000 : ℝ)*base66 + (4275581587009185507/358700000000000000000000000000000 : ℝ)*base68 + (2607728464983185507/358700000000000000000000000000000 : ℝ)*base70 + (2672018627552785507/358700000000000000000000000000000 : ℝ)*base72 + (16877330137469/3587000000000000000000000000 : ℝ)*base74 + (3746104923774985507/358700000000000000000000000000000 : ℝ)*base76 + (2545512195333985507/358700000000000000000000000000000 : ℝ)*base78 + (4240855211925485507/358700000000000000000000000000000 : ℝ)*base80 + (904220276689/3587000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5902123/1250000000000000000000 : ℝ)*base89 + (5902123/1250000000000000000000 : ℝ)*base91 + (5902123/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1125328609037969845563/224187500000000000000000000 : ℝ) := by norm_num
    linear_combination (706111581/100000000000000 : ℝ)*(base19) + (639718301/50000000000000 : ℝ)*(base23) + (13900003/25000000000000 : ℝ)*(upper2) + (20113591/50000000000000 : ℝ)*(upper3) + (323655919/100000000000000 : ℝ)*(upper5) + (441413676433971/10000000000000 : ℝ)*(major0) + (441413676433971/10000000000000 : ℝ)*(major1) + (441413676433971/10000000000000 : ℝ)*(major2) + (32291552087/100000000000000 : ℝ)*(sp1) + (5541951729/25000000000000 : ℝ)*(sp2) + (746294370014991/12500000000000 : ℝ)*(sp4) + (5970321962456261/100000000000000 : ℝ)*(sp5) + (5970331512876411/100000000000000 : ℝ)*(sp6) + (2857918401239927/100000000000000 : ℝ)*(sp7) + (2857918401239927/100000000000000 : ℝ)*(f.failure) + (746294370014991/12500000000000 : ℝ)*(f.sum) + (9504170528647/3587000000000000000000000000 : ℝ)*base66 + (1177377850701150631/358700000000000000000000000000000 : ℝ)*base67 + (1485138814559250631/358700000000000000000000000000000 : ℝ)*base69 + (685427753024550631/358700000000000000000000000000000 : ℝ)*base71 + (943482703039/3587000000000000000000000000 : ℝ)*base73 + (2026180180465049369/358700000000000000000000000000000 : ℝ)*base76 + (2599504985250649369/358700000000000000000000000000000 : ℝ)*base78 + (1732256407361049369/358700000000000000000000000000000 : ℝ)*base80 + (9288028434561/3587000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (36910537/5000000000000000000000 : ℝ)*base89 + (36910537/5000000000000000000000 : ℝ)*base91 + (36910537/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1335_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2783/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1335_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1335_s7_0 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-82001499/400000000 : ℝ)*x 0 + (108260293/200000000 : ℝ)*x 1 + (327777599/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82001499/400000000 : ℝ)^4295 ≤ (6241313619781/50000000000000 : ℝ)^3271 := by
    have hnat : (82001499 : ℕ)^4295*50000000000000^3271 ≤ 6241313619781^3271*400000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82001499 400000000 6241313619781 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108260293/200000000 : ℝ)^4295 ≤ (44667459134817/100000000000000 : ℝ)^3271 := by
    have hnat : (108260293 : ℕ)^4295*100000000000000^3271 ≤ 44667459134817^3271*200000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108260293 200000000 44667459134817 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327777599/625000000 : ℝ)^4295 ≤ (42849913611623/100000000000000 : ℝ)^3271 := by
    have hnat : (327777599 : ℕ)^4295*100000000000000^3271 ≤ 42849913611623^3271*625000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327777599 625000000 42849913611623 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82001499/400000000 : ℝ), (108260293/200000000 : ℝ), (327777599/625000000 : ℝ)] ![(6241313619781/50000000000000 : ℝ), (44667459134817/100000000000000 : ℝ), (42849913611623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82001499/400000000 : ℝ)|^4295 ≤ (6241313619781/50000000000000 : ℝ)^3271
        have hw : |(-82001499/400000000 : ℝ)|=(82001499/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108260293/200000000 : ℝ)|^4295 ≤ (44667459134817/100000000000000 : ℝ)^3271
        have hw : |(108260293/200000000 : ℝ)|=(108260293/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327777599/625000000 : ℝ)|^4295 ≤ (42849913611623/100000000000000 : ℝ)^3271
        have hw : |(327777599/625000000 : ℝ)|=(327777599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s7_1 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674551461/5000000000 : ℝ)*x 0 + (-66747901/312500000 : ℝ)*x 1 + (327777607/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674551461/5000000000 : ℝ)^4295 ≤ (21988124837497/50000000000000 : ℝ)^3271 := by
    have hnat : (2674551461 : ℕ)^4295*50000000000000^3271 ≤ 21988124837497^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674551461 5000000000 21988124837497 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66747901/312500000 : ℝ)^4295 ≤ (6586917660989/50000000000000 : ℝ)^3271 := by
    have hnat : (66747901 : ℕ)^4295*50000000000000^3271 ≤ 6586917660989^3271*312500000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66747901 312500000 6586917660989 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327777607/625000000 : ℝ)^4295 ≤ (42849914984853/100000000000000 : ℝ)^3271 := by
    have hnat : (327777607 : ℕ)^4295*100000000000000^3271 ≤ 42849914984853^3271*625000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327777607 625000000 42849914984853 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674551461/5000000000 : ℝ), (-66747901/312500000 : ℝ), (327777607/625000000 : ℝ)] ![(21988124837497/50000000000000 : ℝ), (6586917660989/50000000000000 : ℝ), (42849914984853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674551461/5000000000 : ℝ)|^4295 ≤ (21988124837497/50000000000000 : ℝ)^3271
        have hw : |(2674551461/5000000000 : ℝ)|=(2674551461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66747901/312500000 : ℝ)|^4295 ≤ (6586917660989/50000000000000 : ℝ)^3271
        have hw : |(-66747901/312500000 : ℝ)|=(66747901/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327777607/625000000 : ℝ)|^4295 ≤ (42849914984853/100000000000000 : ℝ)^3271
        have hw : |(327777607/625000000 : ℝ)|=(327777607/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s7_2 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668638177/1250000000 : ℝ)*x 0 + (1311109993/2500000000 : ℝ)*x 1 + (-1067965907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668638177/1250000000 : ℝ)^4295 ≤ (43976276597553/100000000000000 : ℝ)^3271 := by
    have hnat : (668638177 : ℕ)^4295*100000000000000^3271 ≤ 43976276597553^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668638177 1250000000 43976276597553 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311109993/2500000000 : ℝ)^4295 ≤ (10712474079377/25000000000000 : ℝ)^3271 := by
    have hnat : (1311109993 : ℕ)^4295*25000000000000^3271 ≤ 10712474079377^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311109993 2500000000 10712474079377 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067965907/5000000000 : ℝ)^4295 ≤ (2634765415531/20000000000000 : ℝ)^3271 := by
    have hnat : (1067965907 : ℕ)^4295*20000000000000^3271 ≤ 2634765415531^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067965907 5000000000 2634765415531 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668638177/1250000000 : ℝ), (1311109993/2500000000 : ℝ), (-1067965907/5000000000 : ℝ)] ![(43976276597553/100000000000000 : ℝ), (10712474079377/25000000000000 : ℝ), (2634765415531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668638177/1250000000 : ℝ)|^4295 ≤ (43976276597553/100000000000000 : ℝ)^3271
        have hw : |(668638177/1250000000 : ℝ)|=(668638177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311109993/2500000000 : ℝ)|^4295 ≤ (10712474079377/25000000000000 : ℝ)^3271
        have hw : |(1311109993/2500000000 : ℝ)|=(1311109993/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1067965907/5000000000 : ℝ)|^4295 ≤ (2634765415531/20000000000000 : ℝ)^3271
        have hw : |(-1067965907/5000000000 : ℝ)|=(1067965907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s7_3 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4328458551/10000000000 : ℝ)*x 0 + (2077865053/5000000000 : ℝ)*x 1 + (2253947167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328458551/10000000000 : ℝ)^4295 ≤ (1665159732571/5000000000000 : ℝ)^3271 := by
    have hnat : (4328458551 : ℕ)^4295*5000000000000^3271 ≤ 1665159732571^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328458551 10000000000 1665159732571 5000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2077865053/5000000000 : ℝ)^4295 ≤ (7892295239151/25000000000000 : ℝ)^3271 := by
    have hnat : (2077865053 : ℕ)^4295*25000000000000^3271 ≤ 7892295239151^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077865053 5000000000 7892295239151 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253947167/5000000000 : ℝ)^4295 ≤ (8781906093287/25000000000000 : ℝ)^3271 := by
    have hnat : (2253947167 : ℕ)^4295*25000000000000^3271 ≤ 8781906093287^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253947167 5000000000 8781906093287 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328458551/10000000000 : ℝ), (2077865053/5000000000 : ℝ), (2253947167/5000000000 : ℝ)] ![(1665159732571/5000000000000 : ℝ), (7892295239151/25000000000000 : ℝ), (8781906093287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328458551/10000000000 : ℝ)|^4295 ≤ (1665159732571/5000000000000 : ℝ)^3271
        have hw : |(4328458551/10000000000 : ℝ)|=(4328458551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2077865053/5000000000 : ℝ)|^4295 ≤ (7892295239151/25000000000000 : ℝ)^3271
        have hw : |(2077865053/5000000000 : ℝ)|=(2077865053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253947167/5000000000 : ℝ)|^4295 ≤ (8781906093287/25000000000000 : ℝ)^3271
        have hw : |(2253947167/5000000000 : ℝ)|=(2253947167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s7_4 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-128128073/625000000 : ℝ)*x 0 + (1049008673/2000000000 : ℝ)*x 1 + (108248203/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128128073/625000000 : ℝ)^4295 ≤ (624136036349/5000000000000 : ℝ)^3271 := by
    have hnat : (128128073 : ℕ)^4295*5000000000000^3271 ≤ 624136036349^3271*625000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128128073 625000000 624136036349 5000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049008673/2000000000 : ℝ)^4295 ≤ (42856369850551/100000000000000 : ℝ)^3271 := by
    have hnat : (1049008673 : ℕ)^4295*100000000000000^3271 ≤ 42856369850551^3271*2000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049008673 2000000000 42856369850551 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108248203/200000000 : ℝ)^4295 ≤ (1395653418907/3125000000000 : ℝ)^3271 := by
    have hnat : (108248203 : ℕ)^4295*3125000000000^3271 ≤ 1395653418907^3271*200000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108248203 200000000 1395653418907 3125000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128128073/625000000 : ℝ), (1049008673/2000000000 : ℝ), (108248203/200000000 : ℝ)] ![(624136036349/5000000000000 : ℝ), (42856369850551/100000000000000 : ℝ), (1395653418907/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128128073/625000000 : ℝ)|^4295 ≤ (624136036349/5000000000000 : ℝ)^3271
        have hw : |(-128128073/625000000 : ℝ)|=(128128073/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049008673/2000000000 : ℝ)|^4295 ≤ (42856369850551/100000000000000 : ℝ)^3271
        have hw : |(1049008673/2000000000 : ℝ)|=(1049008673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108248203/200000000 : ℝ)|^4295 ≤ (1395653418907/3125000000000 : ℝ)^3271
        have hw : |(108248203/200000000 : ℝ)|=(108248203/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s7_5 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305719113/10000000000 : ℝ)*x 0 + (-491990507/2500000000 : ℝ)*x 1 + (1082482001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305719113/10000000000 : ℝ)^4295 ≤ (870170402279/2000000000000 : ℝ)^3271 := by
    have hnat : (5305719113 : ℕ)^4295*2000000000000^3271 ≤ 870170402279^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305719113 10000000000 870170402279 2000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491990507/2500000000 : ℝ)^4295 ≤ (11830572026573/100000000000000 : ℝ)^3271 := by
    have hnat : (491990507 : ℕ)^4295*100000000000000^3271 ≤ 11830572026573^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491990507 2500000000 11830572026573 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082482001/2000000000 : ℝ)^4295 ≤ (44660907833983/100000000000000 : ℝ)^3271 := by
    have hnat : (1082482001 : ℕ)^4295*100000000000000^3271 ≤ 44660907833983^3271*2000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082482001 2000000000 44660907833983 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305719113/10000000000 : ℝ), (-491990507/2500000000 : ℝ), (1082482001/2000000000 : ℝ)] ![(870170402279/2000000000000 : ℝ), (11830572026573/100000000000000 : ℝ), (44660907833983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305719113/10000000000 : ℝ)|^4295 ≤ (870170402279/2000000000000 : ℝ)^3271
        have hw : |(5305719113/10000000000 : ℝ)|=(5305719113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491990507/2500000000 : ℝ)|^4295 ≤ (11830572026573/100000000000000 : ℝ)^3271
        have hw : |(-491990507/2500000000 : ℝ)|=(491990507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082482001/2000000000 : ℝ)|^4295 ≤ (44660907833983/100000000000000 : ℝ)^3271
        have hw : |(1082482001/2000000000 : ℝ)|=(1082482001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s7_6 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66321489/125000000 : ℝ)*x 0 + (2706204961/5000000000 : ℝ)*x 1 + (-983981067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66321489/125000000 : ℝ)^4295 ≤ (21754260094661/50000000000000 : ℝ)^3271 := by
    have hnat : (66321489 : ℕ)^4295*50000000000000^3271 ≤ 21754260094661^3271*125000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66321489 125000000 21754260094661 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706204961/5000000000 : ℝ)^4295 ≤ (22330453467349/50000000000000 : ℝ)^3271 := by
    have hnat : (2706204961 : ℕ)^4295*50000000000000^3271 ≤ 22330453467349^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706204961 5000000000 22330453467349 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (983981067/5000000000 : ℝ)^4295 ≤ (1478821607911/12500000000000 : ℝ)^3271 := by
    have hnat : (983981067 : ℕ)^4295*12500000000000^3271 ≤ 1478821607911^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983981067 5000000000 1478821607911 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66321489/125000000 : ℝ), (2706204961/5000000000 : ℝ), (-983981067/5000000000 : ℝ)] ![(21754260094661/50000000000000 : ℝ), (22330453467349/50000000000000 : ℝ), (1478821607911/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66321489/125000000 : ℝ)|^4295 ≤ (21754260094661/50000000000000 : ℝ)^3271
        have hw : |(66321489/125000000 : ℝ)|=(66321489/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706204961/5000000000 : ℝ)|^4295 ≤ (22330453467349/50000000000000 : ℝ)^3271
        have hw : |(2706204961/5000000000 : ℝ)|=(2706204961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-983981067/5000000000 : ℝ)|^4295 ≤ (1478821607911/12500000000000 : ℝ)^3271
        have hw : |(-983981067/5000000000 : ℝ)|=(983981067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s7_7 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082120349/2500000000 : ℝ)*x 0 + (4506636169/10000000000 : ℝ)*x 1 + (2078498733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082120349/2500000000 : ℝ)^4295 ≤ (33303425446623/100000000000000 : ℝ)^3271 := by
    have hnat : (1082120349 : ℕ)^4295*100000000000000^3271 ≤ 33303425446623^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082120349 2500000000 33303425446623 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4506636169/10000000000 : ℝ)^4295 ≤ (35114751475933/100000000000000 : ℝ)^3271 := by
    have hnat : (4506636169 : ℕ)^4295*100000000000000^3271 ≤ 35114751475933^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506636169 10000000000 35114751475933 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078498733/5000000000 : ℝ)^4295 ≤ (31581823059749/100000000000000 : ℝ)^3271 := by
    have hnat : (2078498733 : ℕ)^4295*100000000000000^3271 ≤ 31581823059749^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078498733 5000000000 31581823059749 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082120349/2500000000 : ℝ), (4506636169/10000000000 : ℝ), (2078498733/5000000000 : ℝ)] ![(33303425446623/100000000000000 : ℝ), (35114751475933/100000000000000 : ℝ), (31581823059749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082120349/2500000000 : ℝ)|^4295 ≤ (33303425446623/100000000000000 : ℝ)^3271
        have hw : |(1082120349/2500000000 : ℝ)|=(1082120349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4506636169/10000000000 : ℝ)|^4295 ≤ (35114751475933/100000000000000 : ℝ)^3271
        have hw : |(4506636169/10000000000 : ℝ)|=(4506636169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078498733/5000000000 : ℝ)|^4295 ≤ (31581823059749/100000000000000 : ℝ)^3271
        have hw : |(2078498733/5000000000 : ℝ)|=(2078498733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1335_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2783/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11133/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7351/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2783/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2783/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2783/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14703/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2783/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2783/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14703/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2783/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2783/25000 : ℝ) ^ (2147/512 : ℝ) ≤ (10044741854302137/100000000000000000000 : ℝ) := by
    have hpowers : (2783/25000 : ℝ)^2147 ≤ (10044741854302137/100000000000000000000 : ℝ)^512 := by
      have hnat : (2783 : ℕ)^2147*100000000000000000000^512 ≤ 10044741854302137^512*25000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2783 25000 10044741854302137 100000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2783/25000 : ℝ)) (X := (10044741854302137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14703/100000 : ℝ) ^ (2147/512 : ℝ) ≤ (32257742083418847/100000000000000000000 : ℝ) := by
    have hpowers : (14703/100000 : ℝ)^2147 ≤ (32257742083418847/100000000000000000000 : ℝ)^512 := by
      have hnat : (14703 : ℕ)^2147*100000000000000000000^512 ≤ 32257742083418847^512*100000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14703 100000 32257742083418847 100000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14703/100000 : ℝ)) (X := (32257742083418847/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010044741854302137/50000000000000000000 : ℝ) ≤ (10000479041870221/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (50010044741854302137/50000000000000000000 : ℝ)^512 ≤ (10000479041870221/10000000000000000 : ℝ)^2147 := by
      have hnat : (50010044741854302137 : ℕ)^512*10000000000000000^2147 ≤ 10000479041870221^2147*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010044741854302137 50000000000000000000 10000479041870221 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000479041870221/10000000000000000 : ℝ)) (X := (50010044741854302137/50000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505287810492215123/12500000000000000000 : ℝ) ≤ (2500252158639873/2500000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (12505287810492215123/12500000000000000000 : ℝ)^512 ≤ (2500252158639873/2500000000000000 : ℝ)^2147 := by
      have hnat : (12505287810492215123 : ℕ)^512*2500000000000000^2147 ≤ 2500252158639873^2147*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505287810492215123 12500000000000000000 2500252158639873 2500000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500252158639873/2500000000000000 : ℝ)) (X := (12505287810492215123/12500000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032257742083418847/50000000000000000000 : ℝ) ≤ (10001538227248763/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (50032257742083418847/50000000000000000000 : ℝ)^512 ≤ (10001538227248763/10000000000000000 : ℝ)^2147 := by
      have hnat : (50032257742083418847 : ℕ)^512*10000000000000000^2147 ≤ 10001538227248763^2147*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032257742083418847 50000000000000000000 10001538227248763 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001538227248763/10000000000000000 : ℝ)) (X := (50032257742083418847/50000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10044741854302137/100000000000000000000 : ℝ) ≤ ((35699919806884629647/35710000000000000000 : ℝ)+2*(529592689271/357100000000000 : ℝ)*(2783/25000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (35699919806884629647/35710000000000000000 : ℝ)+2*(529592689271/357100000000000 : ℝ)*(2783/25000 : ℝ)=(10000479041870221/10000000000000000 : ℝ) by norm_num, show 1+2*(10044741854302137/100000000000000000000 : ℝ)=(50010044741854302137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32257742083418847/100000000000000000000 : ℝ)+(10044741854302137/100000000000000000000 : ℝ) ≤ ((35699919806884629647/35710000000000000000 : ℝ)+(529592689271/357100000000000 : ℝ)*((14703/100000 : ℝ)+(2783/25000 : ℝ)))^(2147/512 : ℝ) := by
    rw [show (35699919806884629647/35710000000000000000 : ℝ)+(529592689271/357100000000000 : ℝ)*((14703/100000 : ℝ)+(2783/25000 : ℝ))=(2500252158639873/2500000000000000 : ℝ) by norm_num, show 1+(32257742083418847/100000000000000000000 : ℝ)+(10044741854302137/100000000000000000000 : ℝ)=(12505287810492215123/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32257742083418847/100000000000000000000 : ℝ) ≤ ((35699919806884629647/35710000000000000000 : ℝ)+2*(529592689271/357100000000000 : ℝ)*(14703/100000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (35699919806884629647/35710000000000000000 : ℝ)+2*(529592689271/357100000000000 : ℝ)*(14703/100000 : ℝ)=(10001538227248763/10000000000000000 : ℝ) by norm_num, show 1+2*(32257742083418847/100000000000000000000 : ℝ)=(50032257742083418847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35699919806884629647/35710000000000000000 : ℝ)*(X 1 0+X 2 0)+(529592689271/357100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (2783/25000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (35699919806884629647/35710000000000000000 : ℝ)) (alpha := (529592689271/357100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35699919806884629647/35710000000000000000 : ℝ)*(X 0 1+X 2 1)+(529592689271/357100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (2783/25000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (35699919806884629647/35710000000000000000 : ℝ)) (alpha := (529592689271/357100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35699919806884629647/35710000000000000000 : ℝ)*(X 0 2+X 1 2)+(529592689271/357100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (2783/25000 : ℝ)) (hi := (14703/100000 : ℝ)) (c := (35699919806884629647/35710000000000000000 : ℝ)) (alpha := (529592689271/357100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-82001499/400000000 : ℝ)*X 0 0+(108260293/200000000 : ℝ)*X 0 1+(327777599/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674551461/5000000000 : ℝ)*X 1 0+(-66747901/312500000 : ℝ)*X 1 1+(327777607/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668638177/1250000000 : ℝ)*X 2 0+(1311109993/2500000000 : ℝ)*X 2 1+(-1067965907/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4328458551/10000000000 : ℝ)*X 0 0+(2077865053/5000000000 : ℝ)*X 0 1+(2253947167/5000000000 : ℝ)*X 0 2+(4328458551/10000000000 : ℝ)*X 1 0+(2077865053/5000000000 : ℝ)*X 1 1+(2253947167/5000000000 : ℝ)*X 1 2+(4328458551/10000000000 : ℝ)*X 2 0+(2077865053/5000000000 : ℝ)*X 2 1+(2253947167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-128128073/625000000 : ℝ)*X 0 0+(1049008673/2000000000 : ℝ)*X 0 1+(108248203/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305719113/10000000000 : ℝ)*X 1 0+(-491990507/2500000000 : ℝ)*X 1 1+(1082482001/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66321489/125000000 : ℝ)*X 2 0+(2706204961/5000000000 : ℝ)*X 2 1+(-983981067/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1082120349/2500000000 : ℝ)*X 0 0+(4506636169/10000000000 : ℝ)*X 0 1+(2078498733/5000000000 : ℝ)*X 0 2+(1082120349/2500000000 : ℝ)*X 1 0+(4506636169/10000000000 : ℝ)*X 1 1+(2078498733/5000000000 : ℝ)*X 1 2+(1082120349/2500000000 : ℝ)*X 2 0+(4506636169/10000000000 : ℝ)*X 2 1+(2078498733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (233724639763573025545062147/35710000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (556484177/50000000000000 : ℝ)*(base19) + (1620355611/50000000000000 : ℝ)*(base23) + (170659751/50000000000000 : ℝ)*(lower2) + (35728033/25000000000000 : ℝ)*(upper3) + (1404420317/100000000000000 : ℝ)*(upper5) + (87717429149167/2000000000000 : ℝ)*(major0) + (87717429149167/2000000000000 : ℝ)*(major1) + (87717429149167/2000000000000 : ℝ)*(major2) + (74151213163409/1250000000000 : ℝ)*(sp0) + (741515432871413/12500000000000 : ℝ)*(sp1) + (1186424267045687/20000000000000 : ℝ)*(sp2) + (1419802012939331/50000000000000 : ℝ)*(sp3) + (13761433469/50000000000000 : ℝ)*(sp4) + (7047464597/50000000000000 : ℝ)*(sp7) + (177476132550491/6250000000000 : ℝ)*(f.failure) + (2966062287969829/50000000000000 : ℝ)*(f.sum) + (2441991590357/892750000000000000000000000 : ℝ)*base65 + (237266574186505951/71420000000000000000000000000000 : ℝ)*base68 + (593688253023385951/71420000000000000000000000000000 : ℝ)*base70 + (187946318041825951/71420000000000000000000000000000 : ℝ)*base72 + (12393137311/89275000000000000000000000 : ℝ)*base73 + (1599426354823945951/71420000000000000000000000000000 : ℝ)*base76 + (367190366703934049/71420000000000000000000000000000 : ℝ)*base77 + (730125221294494049/71420000000000000000000000000000 : ℝ)*base79 + (4389031108299/446375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3477621/312500000000000000000 : ℝ)*base89 + (3477621/312500000000000000000 : ℝ)*base91 + (3477621/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5831416222650443513374612713/892750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57390293/2500000000000 : ℝ)*(base19) + (626061131/25000000000000 : ℝ)*(base23) + (752301359/100000000000000 : ℝ)*(lower1) + (54597949/50000000000000 : ℝ)*(upper2) + (203805777/100000000000000 : ℝ)*(upper3) + (237301321/100000000000000 : ℝ)*(upper5) + (2208731879966707/50000000000000 : ℝ)*(major0) + (2208731879966707/50000000000000 : ℝ)*(major1) + (2208731879966707/50000000000000 : ℝ)*(major2) + (618569137/100000000000000 : ℝ)*(sp1) + (2987427424243093/50000000000000 : ℝ)*(sp4) + (597485193430533/10000000000000 : ℝ)*(sp5) + (5974852344241663/100000000000000 : ℝ)*(sp6) + (1430036226824147/50000000000000 : ℝ)*(sp7) + (1430036226824147/50000000000000 : ℝ)*(f.failure) + (2987427424243093/50000000000000 : ℝ)*(f.sum) + (35833677041857/8927500000000000000000000000 : ℝ)*base65 + (14186410482496862429/1785500000000000000000000000000000 : ℝ)*base67 + (70569627027352862429/1785500000000000000000000000000000 : ℝ)*base69 + (16823723516950862429/1785500000000000000000000000000000 : ℝ)*base71 + (13578433350273/2231875000000000000000000000 : ℝ)*base73 + (17659572223084137571/1785500000000000000000000000000000 : ℝ)*base76 + (7297713282512862429/1785500000000000000000000000000000 : ℝ)*base77 + (14762837326561137571/1785500000000000000000000000000000 : ℝ)*base80 + (46276430559671/4463750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (12570643/2500000000000000000000 : ℝ)*base90 + (12570643/2500000000000000000000 : ℝ)*base92 + (12570643/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1335_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14703/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2783/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1335_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1335_box_0 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1882217137/10000000000 : ℝ)*x 0 + (673779339/1250000000 : ℝ)*x 1 + (215609387/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1882217137/10000000000 : ℝ)^4295 ≤ (5579202208223/50000000000000 : ℝ)^3271 := by
    have hnat : (1882217137 : ℕ)^4295*50000000000000^3271 ≤ 5579202208223^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882217137 10000000000 5579202208223 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673779339/1250000000 : ℝ)^4295 ≤ (8884159596311/20000000000000 : ℝ)^3271 := by
    have hnat : (673779339 : ℕ)^4295*20000000000000^3271 ≤ 8884159596311^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673779339 1250000000 8884159596311 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215609387/400000000 : ℝ)^4295 ≤ (44420797581183/100000000000000 : ℝ)^3271 := by
    have hnat : (215609387 : ℕ)^4295*100000000000000^3271 ≤ 44420797581183^3271*400000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215609387 400000000 44420797581183 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1882217137/10000000000 : ℝ), (673779339/1250000000 : ℝ), (215609387/400000000 : ℝ)] ![(5579202208223/50000000000000 : ℝ), (8884159596311/20000000000000 : ℝ), (44420797581183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1882217137/10000000000 : ℝ)|^4295 ≤ (5579202208223/50000000000000 : ℝ)^3271
        have hw : |(-1882217137/10000000000 : ℝ)|=(1882217137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673779339/1250000000 : ℝ)|^4295 ≤ (8884159596311/20000000000000 : ℝ)^3271
        have hw : |(673779339/1250000000 : ℝ)|=(673779339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215609387/400000000 : ℝ)|^4295 ≤ (44420797581183/100000000000000 : ℝ)^3271
        have hw : |(215609387/400000000 : ℝ)|=(215609387/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_1 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642532459/5000000000 : ℝ)*x 0 + (-1013134421/5000000000 : ℝ)*x 1 + (2695117357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642532459/5000000000 : ℝ)^4295 ≤ (5410782853433/12500000000000 : ℝ)^3271 := by
    have hnat : (2642532459 : ℕ)^4295*12500000000000^3271 ≤ 5410782853433^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642532459 5000000000 5410782853433 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1013134421/5000000000 : ℝ)^4295 ≤ (12292939157781/100000000000000 : ℝ)^3271 := by
    have hnat : (1013134421 : ℕ)^4295*100000000000000^3271 ≤ 12292939157781^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013134421 5000000000 12292939157781 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695117357/5000000000 : ℝ)^4295 ≤ (44420798003197/100000000000000 : ℝ)^3271 := by
    have hnat : (2695117357 : ℕ)^4295*100000000000000^3271 ≤ 44420798003197^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695117357 5000000000 44420798003197 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642532459/5000000000 : ℝ), (-1013134421/5000000000 : ℝ), (2695117357/5000000000 : ℝ)] ![(5410782853433/12500000000000 : ℝ), (12292939157781/100000000000000 : ℝ), (44420798003197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642532459/5000000000 : ℝ)|^4295 ≤ (5410782853433/12500000000000 : ℝ)^3271
        have hw : |(2642532459/5000000000 : ℝ)|=(2642532459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1013134421/5000000000 : ℝ)|^4295 ≤ (12292939157781/100000000000000 : ℝ)^3271
        have hw : |(-1013134421/5000000000 : ℝ)|=(1013134421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695117357/5000000000 : ℝ)|^4295 ≤ (44420798003197/100000000000000 : ℝ)^3271
        have hw : |(2695117357/5000000000 : ℝ)|=(2695117357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_2 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057012967/2000000000 : ℝ)*x 0 + (134755869/250000000 : ℝ)*x 1 + (-2026268891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057012967/2000000000 : ℝ)^4295 ≤ (5410782741857/12500000000000 : ℝ)^3271 := by
    have hnat : (1057012967 : ℕ)^4295*12500000000000^3271 ≤ 5410782741857^3271*2000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057012967 2000000000 5410782741857 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134755869/250000000 : ℝ)^4295 ≤ (11105199625239/25000000000000 : ℝ)^3271 := by
    have hnat : (134755869 : ℕ)^4295*25000000000000^3271 ≤ 11105199625239^3271*250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134755869 250000000 11105199625239 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2026268891/10000000000 : ℝ)^4295 ≤ (3073234887029/25000000000000 : ℝ)^3271 := by
    have hnat : (2026268891 : ℕ)^4295*25000000000000^3271 ≤ 3073234887029^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2026268891 10000000000 3073234887029 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057012967/2000000000 : ℝ), (134755869/250000000 : ℝ), (-2026268891/10000000000 : ℝ)] ![(5410782741857/12500000000000 : ℝ), (11105199625239/25000000000000 : ℝ), (3073234887029/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057012967/2000000000 : ℝ)|^4295 ≤ (5410782741857/12500000000000 : ℝ)^3271
        have hw : |(1057012967/2000000000 : ℝ)|=(1057012967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134755869/250000000 : ℝ)|^4295 ≤ (11105199625239/25000000000000 : ℝ)^3271
        have hw : |(134755869/250000000 : ℝ)|=(134755869/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2026268891/10000000000 : ℝ)|^4295 ≤ (3073234887029/25000000000000 : ℝ)^3271
        have hw : |(-2026268891/10000000000 : ℝ)|=(2026268891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_3 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (559601983/1250000000 : ℝ)*x 0 + (66534071/156250000 : ℝ)*x 1 + (2129090331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559601983/1250000000 : ℝ)^4295 ≤ (34809975258569/100000000000000 : ℝ)^3271 := by
    have hnat : (559601983 : ℕ)^4295*100000000000000^3271 ≤ 34809975258569^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559601983 1250000000 34809975258569 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66534071/156250000 : ℝ)^4295 ≤ (4074376471383/12500000000000 : ℝ)^3271 := by
    have hnat : (66534071 : ℕ)^4295*12500000000000^3271 ≤ 4074376471383^3271*156250000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66534071 156250000 4074376471383 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2129090331/5000000000 : ℝ)^4295 ≤ (8148753239271/25000000000000 : ℝ)^3271 := by
    have hnat : (2129090331 : ℕ)^4295*25000000000000^3271 ≤ 8148753239271^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129090331 5000000000 8148753239271 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(559601983/1250000000 : ℝ), (66534071/156250000 : ℝ), (2129090331/5000000000 : ℝ)] ![(34809975258569/100000000000000 : ℝ), (4074376471383/12500000000000 : ℝ), (8148753239271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(559601983/1250000000 : ℝ)|^4295 ≤ (34809975258569/100000000000000 : ℝ)^3271
        have hw : |(559601983/1250000000 : ℝ)|=(559601983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(66534071/156250000 : ℝ)|^4295 ≤ (4074376471383/12500000000000 : ℝ)^3271
        have hw : |(66534071/156250000 : ℝ)|=(66534071/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2129090331/5000000000 : ℝ)|^4295 ≤ (8148753239271/25000000000000 : ℝ)^3271
        have hw : |(2129090331/5000000000 : ℝ)|=(2129090331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_4 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1110304151/5000000000 : ℝ)*x 0 + (105295337/200000000 : ℝ)*x 1 + (210590651/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1110304151/5000000000 : ℝ)^4295 ≤ (1386380108923/10000000000000 : ℝ)^3271 := by
    have hnat : (1110304151 : ℕ)^4295*10000000000000^3271 ≤ 1386380108923^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110304151 5000000000 1386380108923 10000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105295337/200000000 : ℝ)^4295 ≤ (43068102537763/100000000000000 : ℝ)^3271 := by
    have hnat : (105295337 : ℕ)^4295*100000000000000^3271 ≤ 43068102537763^3271*200000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105295337 200000000 43068102537763 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210590651/400000000 : ℝ)^4295 ≤ (21534048180741/50000000000000 : ℝ)^3271 := by
    have hnat : (210590651 : ℕ)^4295*50000000000000^3271 ≤ 21534048180741^3271*400000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210590651 400000000 21534048180741 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1110304151/5000000000 : ℝ), (105295337/200000000 : ℝ), (210590651/400000000 : ℝ)] ![(1386380108923/10000000000000 : ℝ), (43068102537763/100000000000000 : ℝ), (21534048180741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1110304151/5000000000 : ℝ)|^4295 ≤ (1386380108923/10000000000000 : ℝ)^3271
        have hw : |(-1110304151/5000000000 : ℝ)|=(1110304151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105295337/200000000 : ℝ)|^4295 ≤ (43068102537763/100000000000000 : ℝ)^3271
        have hw : |(105295337/200000000 : ℝ)|=(105295337/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210590651/400000000 : ℝ)|^4295 ≤ (21534048180741/50000000000000 : ℝ)^3271
        have hw : |(210590651/400000000 : ℝ)|=(210590651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_5 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107464341/200000000 : ℝ)*x 0 + (-2076565823/10000000000 : ℝ)*x 1 + (2632383431/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107464341/200000000 : ℝ)^4295 ≤ (1382398234717/3125000000000 : ℝ)^3271 := by
    have hnat : (107464341 : ℕ)^4295*3125000000000^3271 ≤ 1382398234717^3271*200000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107464341 200000000 1382398234717 3125000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076565823/10000000000 : ℝ)^4295 ≤ (6347576903879/50000000000000 : ℝ)^3271 := by
    have hnat : (2076565823 : ℕ)^4295*50000000000000^3271 ≤ 6347576903879^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076565823 10000000000 6347576903879 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632383431/5000000000 : ℝ)^4295 ≤ (43068102666659/100000000000000 : ℝ)^3271 := by
    have hnat : (2632383431 : ℕ)^4295*100000000000000^3271 ≤ 43068102666659^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632383431 5000000000 43068102666659 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107464341/200000000 : ℝ), (-2076565823/10000000000 : ℝ), (2632383431/5000000000 : ℝ)] ![(1382398234717/3125000000000 : ℝ), (6347576903879/50000000000000 : ℝ), (43068102666659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107464341/200000000 : ℝ)|^4295 ≤ (1382398234717/3125000000000 : ℝ)^3271
        have hw : |(107464341/200000000 : ℝ)|=(107464341/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076565823/10000000000 : ℝ)|^4295 ≤ (6347576903879/50000000000000 : ℝ)^3271
        have hw : |(-2076565823/10000000000 : ℝ)|=(2076565823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632383431/5000000000 : ℝ)|^4295 ≤ (43068102666659/100000000000000 : ℝ)^3271
        have hw : |(2632383431/5000000000 : ℝ)|=(2632383431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_6 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671652203/1250000000 : ℝ)*x 0 + (42118133/80000000 : ℝ)*x 1 + (-259570671/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671652203/1250000000 : ℝ)^4295 ≤ (22118374857983/50000000000000 : ℝ)^3271 := by
    have hnat : (671652203 : ℕ)^4295*50000000000000^3271 ≤ 22118374857983^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671652203 1250000000 22118374857983 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42118133/80000000 : ℝ)^4295 ≤ (43068100120957/100000000000000 : ℝ)^3271 := by
    have hnat : (42118133 : ℕ)^4295*100000000000000^3271 ≤ 43068100120957^3271*80000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42118133 80000000 43068100120957 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259570671/1250000000 : ℝ)^4295 ≤ (12695150155291/100000000000000 : ℝ)^3271 := by
    have hnat : (259570671 : ℕ)^4295*100000000000000^3271 ≤ 12695150155291^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259570671 1250000000 12695150155291 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671652203/1250000000 : ℝ), (42118133/80000000 : ℝ), (-259570671/1250000000 : ℝ)] ![(22118374857983/50000000000000 : ℝ), (43068100120957/100000000000000 : ℝ), (12695150155291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671652203/1250000000 : ℝ)|^4295 ≤ (22118374857983/50000000000000 : ℝ)^3271
        have hw : |(671652203/1250000000 : ℝ)|=(671652203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42118133/80000000 : ℝ)|^4295 ≤ (43068100120957/100000000000000 : ℝ)^3271
        have hw : |(42118133/80000000 : ℝ)|=(42118133/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259570671/1250000000 : ℝ)|^4295 ≤ (12695150155291/100000000000000 : ℝ)^3271
        have hw : |(-259570671/1250000000 : ℝ)|=(259570671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_7 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4179179293/10000000000 : ℝ)*x 0 + (2203472411/5000000000 : ℝ)*x 1 + (4406945271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4179179293/10000000000 : ℝ)^4295 ≤ (31803285212597/100000000000000 : ℝ)^3271 := by
    have hnat : (4179179293 : ℕ)^4295*100000000000000^3271 ≤ 31803285212597^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179179293 10000000000 31803285212597 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2203472411/5000000000 : ℝ)^4295 ≤ (34098355110073/100000000000000 : ℝ)^3271 := by
    have hnat : (2203472411 : ℕ)^4295*100000000000000^3271 ≤ 34098355110073^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203472411 5000000000 34098355110073 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4406945271/10000000000 : ℝ)^4295 ≤ (34098359671753/100000000000000 : ℝ)^3271 := by
    have hnat : (4406945271 : ℕ)^4295*100000000000000^3271 ≤ 34098359671753^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4406945271 10000000000 34098359671753 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4179179293/10000000000 : ℝ), (2203472411/5000000000 : ℝ), (4406945271/10000000000 : ℝ)] ![(31803285212597/100000000000000 : ℝ), (34098355110073/100000000000000 : ℝ), (34098359671753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4179179293/10000000000 : ℝ)|^4295 ≤ (31803285212597/100000000000000 : ℝ)^3271
        have hw : |(4179179293/10000000000 : ℝ)|=(4179179293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2203472411/5000000000 : ℝ)|^4295 ≤ (34098355110073/100000000000000 : ℝ)^3271
        have hw : |(2203472411/5000000000 : ℝ)|=(2203472411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4406945271/10000000000 : ℝ)|^4295 ≤ (34098359671753/100000000000000 : ℝ)^3271
        have hw : |(4406945271/10000000000 : ℝ)|=(4406945271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_8 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074782829/5000000000 : ℝ)*x 0 + (5178423543/10000000000 : ℝ)*x 1 + (540425771/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074782829/5000000000 : ℝ)^4295 ≤ (13284351584307/100000000000000 : ℝ)^3271 := by
    have hnat : (1074782829 : ℕ)^4295*100000000000000^3271 ≤ 13284351584307^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074782829 5000000000 13284351584307 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178423543/10000000000 : ℝ)^4295 ≤ (42143047932021/100000000000000 : ℝ)^3271 := by
    have hnat : (5178423543 : ℕ)^4295*100000000000000^3271 ≤ 42143047932021^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178423543 10000000000 42143047932021 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540425771/1000000000 : ℝ)^4295 ≤ (696446882313/1562500000000 : ℝ)^3271 := by
    have hnat : (540425771 : ℕ)^4295*1562500000000^3271 ≤ 696446882313^3271*1000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540425771 1000000000 696446882313 1562500000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074782829/5000000000 : ℝ), (5178423543/10000000000 : ℝ), (540425771/1000000000 : ℝ)] ![(13284351584307/100000000000000 : ℝ), (42143047932021/100000000000000 : ℝ), (696446882313/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074782829/5000000000 : ℝ)|^4295 ≤ (13284351584307/100000000000000 : ℝ)^3271
        have hw : |(-1074782829/5000000000 : ℝ)|=(1074782829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178423543/10000000000 : ℝ)|^4295 ≤ (42143047932021/100000000000000 : ℝ)^3271
        have hw : |(5178423543/10000000000 : ℝ)|=(5178423543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540425771/1000000000 : ℝ)|^4295 ≤ (696446882313/1562500000000 : ℝ)^3271
        have hw : |(540425771/1000000000 : ℝ)|=(540425771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_9 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318801697/2500000000 : ℝ)*x 0 + (-63141057/312500000 : ℝ)*x 1 + (5404258457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318801697/2500000000 : ℝ)^4295 ≤ (43180276447577/100000000000000 : ℝ)^3271 := by
    have hnat : (1318801697 : ℕ)^4295*100000000000000^3271 ≤ 43180276447577^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318801697 2500000000 43180276447577 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63141057/312500000 : ℝ)^4295 ≤ (12247114974463/100000000000000 : ℝ)^3271 := by
    have hnat : (63141057 : ℕ)^4295*100000000000000^3271 ≤ 12247114974463^3271*312500000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63141057 312500000 12247114974463 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404258457/10000000000 : ℝ)^4295 ≤ (5571576069723/12500000000000 : ℝ)^3271 := by
    have hnat : (5404258457 : ℕ)^4295*12500000000000^3271 ≤ 5571576069723^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404258457 10000000000 5571576069723 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318801697/2500000000 : ℝ), (-63141057/312500000 : ℝ), (5404258457/10000000000 : ℝ)] ![(43180276447577/100000000000000 : ℝ), (12247114974463/100000000000000 : ℝ), (5571576069723/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318801697/2500000000 : ℝ)|^4295 ≤ (43180276447577/100000000000000 : ℝ)^3271
        have hw : |(1318801697/2500000000 : ℝ)|=(1318801697/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-63141057/312500000 : ℝ)|^4295 ≤ (12247114974463/100000000000000 : ℝ)^3271
        have hw : |(-63141057/312500000 : ℝ)|=(63141057/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404258457/10000000000 : ℝ)|^4295 ≤ (5571576069723/12500000000000 : ℝ)^3271
        have hw : |(5404258457/10000000000 : ℝ)|=(5404258457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_10 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211008303/400000000 : ℝ)*x 0 + (2702128877/5000000000 : ℝ)*x 1 + (-1010256859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211008303/400000000 : ℝ)^4295 ≤ (43180284906271/100000000000000 : ℝ)^3271 := by
    have hnat : (211008303 : ℕ)^4295*100000000000000^3271 ≤ 43180284906271^3271*400000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211008303 400000000 43180284906271 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702128877/5000000000 : ℝ)^4295 ≤ (44572600944537/100000000000000 : ℝ)^3271 := by
    have hnat : (2702128877 : ℕ)^4295*100000000000000^3271 ≤ 44572600944537^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702128877 5000000000 44572600944537 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1010256859/5000000000 : ℝ)^4295 ≤ (95680579147/781250000000 : ℝ)^3271 := by
    have hnat : (1010256859 : ℕ)^4295*781250000000^3271 ≤ 95680579147^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010256859 5000000000 95680579147 781250000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211008303/400000000 : ℝ), (2702128877/5000000000 : ℝ), (-1010256859/5000000000 : ℝ)] ![(43180284906271/100000000000000 : ℝ), (44572600944537/100000000000000 : ℝ), (95680579147/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211008303/400000000 : ℝ)|^4295 ≤ (43180284906271/100000000000000 : ℝ)^3271
        have hw : |(211008303/400000000 : ℝ)|=(211008303/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702128877/5000000000 : ℝ)|^4295 ≤ (44572600944537/100000000000000 : ℝ)^3271
        have hw : |(2702128877/5000000000 : ℝ)|=(2702128877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1010256859/5000000000 : ℝ)|^4295 ≤ (95680579147/781250000000 : ℝ)^3271
        have hw : |(-1010256859/5000000000 : ℝ)|=(1010256859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_11 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4509522071/10000000000 : ℝ)*x 0 + (2120769931/5000000000 : ℝ)*x 1 + (530192517/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4509522071/10000000000 : ℝ)^4295 ≤ (35144280209903/100000000000000 : ℝ)^3271 := by
    have hnat : (4509522071 : ℕ)^4295*100000000000000^3271 ≤ 35144280209903^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509522071 10000000000 35144280209903 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2120769931/5000000000 : ℝ)^4295 ≤ (32427858515283/100000000000000 : ℝ)^3271 := by
    have hnat : (2120769931 : ℕ)^4295*100000000000000^3271 ≤ 32427858515283^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2120769931 5000000000 32427858515283 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530192517/1250000000 : ℝ)^4295 ≤ (16213930632943/50000000000000 : ℝ)^3271 := by
    have hnat : (530192517 : ℕ)^4295*50000000000000^3271 ≤ 16213930632943^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530192517 1250000000 16213930632943 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4509522071/10000000000 : ℝ), (2120769931/5000000000 : ℝ), (530192517/1250000000 : ℝ)] ![(35144280209903/100000000000000 : ℝ), (32427858515283/100000000000000 : ℝ), (16213930632943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4509522071/10000000000 : ℝ)|^4295 ≤ (35144280209903/100000000000000 : ℝ)^3271
        have hw : |(4509522071/10000000000 : ℝ)|=(4509522071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2120769931/5000000000 : ℝ)|^4295 ≤ (32427858515283/100000000000000 : ℝ)^3271
        have hw : |(2120769931/5000000000 : ℝ)|=(2120769931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530192517/1250000000 : ℝ)|^4295 ≤ (16213930632943/50000000000000 : ℝ)^3271
        have hw : |(530192517/1250000000 : ℝ)|=(530192517/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_12 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-61050347/312500000 : ℝ)*x 0 + (5474356281/10000000000 : ℝ)*x 1 + (5253702693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61050347/312500000 : ℝ)^4295 ≤ (2929355498509/25000000000000 : ℝ)^3271 := by
    have hnat : (61050347 : ℕ)^4295*25000000000000^3271 ≤ 2929355498509^3271*312500000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61050347 312500000 2929355498509 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474356281/10000000000 : ℝ)^4295 ≤ (45333280419249/100000000000000 : ℝ)^3271 := by
    have hnat : (5474356281 : ℕ)^4295*100000000000000^3271 ≤ 45333280419249^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474356281 10000000000 45333280419249 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253702693/10000000000 : ℝ)^4295 ≤ (5368662196419/12500000000000 : ℝ)^3271 := by
    have hnat : (5253702693 : ℕ)^4295*12500000000000^3271 ≤ 5368662196419^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253702693 10000000000 5368662196419 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61050347/312500000 : ℝ), (5474356281/10000000000 : ℝ), (5253702693/10000000000 : ℝ)] ![(2929355498509/25000000000000 : ℝ), (45333280419249/100000000000000 : ℝ), (5368662196419/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61050347/312500000 : ℝ)|^4295 ≤ (2929355498509/25000000000000 : ℝ)^3271
        have hw : |(-61050347/312500000 : ℝ)|=(61050347/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474356281/10000000000 : ℝ)|^4295 ≤ (45333280419249/100000000000000 : ℝ)^3271
        have hw : |(5474356281/10000000000 : ℝ)|=(5474356281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253702693/10000000000 : ℝ)|^4295 ≤ (5368662196419/12500000000000 : ℝ)^3271
        have hw : |(5253702693/10000000000 : ℝ)|=(5253702693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_13 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215239531/400000000 : ℝ)*x 0 + (-416179323/2000000000 : ℝ)*x 1 + (5253702851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215239531/400000000 : ℝ)^4295 ≤ (8864154113299/20000000000000 : ℝ)^3271 := by
    have hnat : (215239531 : ℕ)^4295*20000000000000^3271 ≤ 8864154113299^3271*400000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215239531 400000000 8864154113299 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416179323/2000000000 : ℝ)^4295 ≤ (12729930149723/100000000000000 : ℝ)^3271 := by
    have hnat : (416179323 : ℕ)^4295*100000000000000^3271 ≤ 12729930149723^3271*2000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416179323 2000000000 12729930149723 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253702851/10000000000 : ℝ)^4295 ≤ (42949299267369/100000000000000 : ℝ)^3271 := by
    have hnat : (5253702851 : ℕ)^4295*100000000000000^3271 ≤ 42949299267369^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253702851 10000000000 42949299267369 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215239531/400000000 : ℝ), (-416179323/2000000000 : ℝ), (5253702851/10000000000 : ℝ)] ![(8864154113299/20000000000000 : ℝ), (12729930149723/100000000000000 : ℝ), (42949299267369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215239531/400000000 : ℝ)|^4295 ≤ (8864154113299/20000000000000 : ℝ)^3271
        have hw : |(215239531/400000000 : ℝ)|=(215239531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-416179323/2000000000 : ℝ)|^4295 ≤ (12729930149723/100000000000000 : ℝ)^3271
        have hw : |(-416179323/2000000000 : ℝ)|=(416179323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253702851/10000000000 : ℝ)|^4295 ≤ (42949299267369/100000000000000 : ℝ)^3271
        have hw : |(5253702851/10000000000 : ℝ)|=(5253702851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_14 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380988199/10000000000 : ℝ)*x 0 + (5253702697/10000000000 : ℝ)*x 1 + (-2080896923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380988199/10000000000 : ℝ)^4295 ≤ (5540096218069/12500000000000 : ℝ)^3271 := by
    have hnat : (5380988199 : ℕ)^4295*12500000000000^3271 ≤ 5540096218069^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380988199 10000000000 5540096218069 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253702697/10000000000 : ℝ)^4295 ≤ (42949297614289/100000000000000 : ℝ)^3271 := by
    have hnat : (5253702697 : ℕ)^4295*100000000000000^3271 ≤ 42949297614289^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253702697 10000000000 42949297614289 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2080896923/10000000000 : ℝ)^4295 ≤ (509197304951/4000000000000 : ℝ)^3271 := by
    have hnat : (2080896923 : ℕ)^4295*4000000000000^3271 ≤ 509197304951^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080896923 10000000000 509197304951 4000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380988199/10000000000 : ℝ), (5253702697/10000000000 : ℝ), (-2080896923/10000000000 : ℝ)] ![(5540096218069/12500000000000 : ℝ), (42949297614289/100000000000000 : ℝ), (509197304951/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380988199/10000000000 : ℝ)|^4295 ≤ (5540096218069/12500000000000 : ℝ)^3271
        have hw : |(5380988199/10000000000 : ℝ)|=(5380988199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253702697/10000000000 : ℝ)|^4295 ≤ (42949297614289/100000000000000 : ℝ)^3271
        have hw : |(5253702697/10000000000 : ℝ)|=(5253702697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2080896923/10000000000 : ℝ)|^4295 ≤ (509197304951/4000000000000 : ℝ)^3271
        have hw : |(-2080896923/10000000000 : ℝ)|=(2080896923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_box_15 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2076243039/5000000000 : ℝ)*x 0 + (110501313/250000000 : ℝ)*x 1 + (4420052519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2076243039/5000000000 : ℝ)^4295 ≤ (31536826797263/100000000000000 : ℝ)^3271 := by
    have hnat : (2076243039 : ℕ)^4295*100000000000000^3271 ≤ 31536826797263^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076243039 5000000000 31536826797263 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110501313/250000000 : ℝ)^4295 ≤ (17115793298373/50000000000000 : ℝ)^3271 := by
    have hnat : (110501313 : ℕ)^4295*50000000000000^3271 ≤ 17115793298373^3271*250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110501313 250000000 17115793298373 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4420052519/10000000000 : ℝ)^4295 ≤ (34231586586577/100000000000000 : ℝ)^3271 := by
    have hnat : (4420052519 : ℕ)^4295*100000000000000^3271 ≤ 34231586586577^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4420052519 10000000000 34231586586577 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2076243039/5000000000 : ℝ), (110501313/250000000 : ℝ), (4420052519/10000000000 : ℝ)] ![(31536826797263/100000000000000 : ℝ), (17115793298373/50000000000000 : ℝ), (34231586586577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2076243039/5000000000 : ℝ)|^4295 ≤ (31536826797263/100000000000000 : ℝ)^3271
        have hw : |(2076243039/5000000000 : ℝ)|=(2076243039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(110501313/250000000 : ℝ)|^4295 ≤ (17115793298373/50000000000000 : ℝ)^3271
        have hw : |(110501313/250000000 : ℝ)|=(110501313/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4420052519/10000000000 : ℝ)|^4295 ≤ (34231586586577/100000000000000 : ℝ)^3271
        have hw : |(4420052519/10000000000 : ℝ)|=(4420052519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1335_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62853/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(3683/6250 : ℝ) ∧ (79913/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (3373/4000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11133/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7351/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11133/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11133/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7351/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11133/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11133/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7351/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11133/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11133/100000 : ℝ) ^ (2147/512 : ℝ) ≤ (10048526192635819/100000000000000000000 : ℝ) := by
    have hpowers : (11133/100000 : ℝ)^2147 ≤ (10048526192635819/100000000000000000000 : ℝ)^512 := by
      have hnat : (11133 : ℕ)^2147*100000000000000000000^512 ≤ 10048526192635819^512*100000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11133 100000 10048526192635819 100000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11133/100000 : ℝ)) (X := (10048526192635819/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7351/50000 : ℝ) ^ (2147/512 : ℝ) ≤ (16124271517245621/50000000000000000000 : ℝ) := by
    have hpowers : (7351/50000 : ℝ)^2147 ≤ (16124271517245621/50000000000000000000 : ℝ)^512 := by
      have hnat : (7351 : ℕ)^2147*50000000000000000000^512 ≤ 16124271517245621^512*50000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7351 50000 16124271517245621 50000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7351/50000 : ℝ)) (X := (16124271517245621/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010048526192635819/50000000000000000000 : ℝ) ≤ (10000479222334571/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (50010048526192635819/50000000000000000000 : ℝ)^512 ≤ (10000479222334571/10000000000000000 : ℝ)^2147 := by
      have hnat : (50010048526192635819 : ℕ)^512*10000000000000000^2147 ≤ 10000479222334571^2147*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010048526192635819 50000000000000000000 10000479222334571 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000479222334571/10000000000000000 : ℝ)) (X := (50010048526192635819/50000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100042297069227127061/100000000000000000000 : ℝ) ≤ (10001008505475229/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (100042297069227127061/100000000000000000000 : ℝ)^512 ≤ (10001008505475229/10000000000000000 : ℝ)^2147 := by
      have hnat : (100042297069227127061 : ℕ)^512*10000000000000000^2147 ≤ 10001008505475229^2147*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100042297069227127061 100000000000000000000 10001008505475229 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001008505475229/10000000000000000 : ℝ)) (X := (100042297069227127061/100000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016124271517245621/25000000000000000000 : ℝ) ≤ (10001537788615887/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (25016124271517245621/25000000000000000000 : ℝ)^512 ≤ (10001537788615887/10000000000000000 : ℝ)^2147 := by
      have hnat : (25016124271517245621 : ℕ)^512*10000000000000000^2147 ≤ 10001537788615887^2147*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016124271517245621 25000000000000000000 10001537788615887 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001537788615887/10000000000000000 : ℝ)) (X := (25016124271517245621/25000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10048526192635819/100000000000000000000 : ℝ) ≤ ((35679925326102192871/35690000000000000000 : ℝ)+2*(264641570329/178450000000000 : ℝ)*(11133/100000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (35679925326102192871/35690000000000000000 : ℝ)+2*(264641570329/178450000000000 : ℝ)*(11133/100000 : ℝ)=(10000479222334571/10000000000000000 : ℝ) by norm_num, show 1+2*(10048526192635819/100000000000000000000 : ℝ)=(50010048526192635819/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16124271517245621/50000000000000000000 : ℝ)+(10048526192635819/100000000000000000000 : ℝ) ≤ ((35679925326102192871/35690000000000000000 : ℝ)+(264641570329/178450000000000 : ℝ)*((7351/50000 : ℝ)+(11133/100000 : ℝ)))^(2147/512 : ℝ) := by
    rw [show (35679925326102192871/35690000000000000000 : ℝ)+(264641570329/178450000000000 : ℝ)*((7351/50000 : ℝ)+(11133/100000 : ℝ))=(10001008505475229/10000000000000000 : ℝ) by norm_num, show 1+(16124271517245621/50000000000000000000 : ℝ)+(10048526192635819/100000000000000000000 : ℝ)=(100042297069227127061/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16124271517245621/50000000000000000000 : ℝ) ≤ ((35679925326102192871/35690000000000000000 : ℝ)+2*(264641570329/178450000000000 : ℝ)*(7351/50000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (35679925326102192871/35690000000000000000 : ℝ)+2*(264641570329/178450000000000 : ℝ)*(7351/50000 : ℝ)=(10001537788615887/10000000000000000 : ℝ) by norm_num, show 1+2*(16124271517245621/50000000000000000000 : ℝ)=(25016124271517245621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35679925326102192871/35690000000000000000 : ℝ)*(X 1 0+X 2 0)+(264641570329/178450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (35679925326102192871/35690000000000000000 : ℝ)) (alpha := (264641570329/178450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35679925326102192871/35690000000000000000 : ℝ)*(X 0 1+X 2 1)+(264641570329/178450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (35679925326102192871/35690000000000000000 : ℝ)) (alpha := (264641570329/178450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35679925326102192871/35690000000000000000 : ℝ)*(X 0 2+X 1 2)+(264641570329/178450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (11133/100000 : ℝ)) (hi := (7351/50000 : ℝ)) (c := (35679925326102192871/35690000000000000000 : ℝ)) (alpha := (264641570329/178450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1882217137/10000000000 : ℝ)*X 0 0+(673779339/1250000000 : ℝ)*X 0 1+(215609387/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642532459/5000000000 : ℝ)*X 1 0+(-1013134421/5000000000 : ℝ)*X 1 1+(2695117357/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1057012967/2000000000 : ℝ)*X 2 0+(134755869/250000000 : ℝ)*X 2 1+(-2026268891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((559601983/1250000000 : ℝ)*X 0 0+(66534071/156250000 : ℝ)*X 0 1+(2129090331/5000000000 : ℝ)*X 0 2+(559601983/1250000000 : ℝ)*X 1 0+(66534071/156250000 : ℝ)*X 1 1+(2129090331/5000000000 : ℝ)*X 1 2+(559601983/1250000000 : ℝ)*X 2 0+(66534071/156250000 : ℝ)*X 2 1+(2129090331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1110304151/5000000000 : ℝ)*X 0 0+(105295337/200000000 : ℝ)*X 0 1+(210590651/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((107464341/200000000 : ℝ)*X 1 0+(-2076565823/10000000000 : ℝ)*X 1 1+(2632383431/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671652203/1250000000 : ℝ)*X 2 0+(42118133/80000000 : ℝ)*X 2 1+(-259570671/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4179179293/10000000000 : ℝ)*X 0 0+(2203472411/5000000000 : ℝ)*X 0 1+(4406945271/10000000000 : ℝ)*X 0 2+(4179179293/10000000000 : ℝ)*X 1 0+(2203472411/5000000000 : ℝ)*X 1 1+(4406945271/10000000000 : ℝ)*X 1 2+(4179179293/10000000000 : ℝ)*X 2 0+(2203472411/5000000000 : ℝ)*X 2 1+(4406945271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1074782829/5000000000 : ℝ)*X 0 0+(5178423543/10000000000 : ℝ)*X 0 1+(540425771/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1318801697/2500000000 : ℝ)*X 1 0+(-63141057/312500000 : ℝ)*X 1 1+(5404258457/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((211008303/400000000 : ℝ)*X 2 0+(2702128877/5000000000 : ℝ)*X 2 1+(-1010256859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4509522071/10000000000 : ℝ)*X 0 0+(2120769931/5000000000 : ℝ)*X 0 1+(530192517/1250000000 : ℝ)*X 0 2+(4509522071/10000000000 : ℝ)*X 1 0+(2120769931/5000000000 : ℝ)*X 1 1+(530192517/1250000000 : ℝ)*X 1 2+(4509522071/10000000000 : ℝ)*X 2 0+(2120769931/5000000000 : ℝ)*X 2 1+(530192517/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-61050347/312500000 : ℝ)*X 0 0+(5474356281/10000000000 : ℝ)*X 0 1+(5253702693/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((215239531/400000000 : ℝ)*X 1 0+(-416179323/2000000000 : ℝ)*X 1 1+(5253702851/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380988199/10000000000 : ℝ)*X 2 0+(5253702697/10000000000 : ℝ)*X 2 1+(-2080896923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2076243039/5000000000 : ℝ)*X 0 0+(110501313/250000000 : ℝ)*X 0 1+(4420052519/10000000000 : ℝ)*X 0 2+(2076243039/5000000000 : ℝ)*X 1 0+(110501313/250000000 : ℝ)*X 1 1+(4420052519/10000000000 : ℝ)*X 1 2+(2076243039/5000000000 : ℝ)*X 2 0+(110501313/250000000 : ℝ)*X 2 1+(4420052519/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62853/100000 : ℝ) ≤ (-2243123095530771946503056061/3569000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7938133/5000000000000 : ℝ)*(upper0) + (72826943/100000000000000 : ℝ)*(lower1) + (143517259/50000000000000 : ℝ)*(lower2) + (582534380997129/20000000000000 : ℝ)*(major0) + (582534380997129/20000000000000 : ℝ)*(major1) + (582534380997129/20000000000000 : ℝ)*(major2) + (920278723/12500000000000 : ℝ)*(sp3) + (990121557472943/25000000000000 : ℝ)*(sp4) + (1980223691455487/50000000000000 : ℝ)*(sp5) + (990092636984383/25000000000000 : ℝ)*(sp6) + (1885792529898887/100000000000000 : ℝ)*(sp7) + (3874775507/50000000000000 : ℝ)*(sp8) + (11649132953/25000000000000 : ℝ)*(sp13) + (24686301051/20000000000000 : ℝ)*(sp14) + (1885799892128671/100000000000000 : ℝ)*(f.failure) + (1980246989721393/50000000000000 : ℝ)*(f.sum) + (16191203079477/3569000000000000000000000000 : ℝ)*base66 + (2341311800657867359/713800000000000000000000000000000 : ℝ)*base67 + (1298277822818467359/713800000000000000000000000000000 : ℝ)*base69 + (1113765061158867359/713800000000000000000000000000000 : ℝ)*base71 + (1498967685669/71380000000000000000000000 : ℝ)*base74 + (1453087375749532641/713800000000000000000000000000000 : ℝ)*base76 + (2876047672180532641/713800000000000000000000000000000 : ℝ)*base78 + (22735311230217532641/713800000000000000000000000000000 : ℝ)*base80 + (4119021984023/1784500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4103201/5000000000000000000000 : ℝ)*base89 + (4103201/5000000000000000000000 : ℝ)*base91 + (4103201/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (3683/6250 : ℝ) ≤ (1051606227505520870738856931285047/1784500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1201313/25000000000000 : ℝ)*(lower1) + (36727937/100000000000000 : ℝ)*(upper2) + (131423/50000000000000 : ℝ)*(upper5) + (2981130066877819/100000000000000 : ℝ)*(major0) + (2981130066877819/100000000000000 : ℝ)*(major1) + (2981130066877819/100000000000000 : ℝ)*(major2) + (1003123324493651/25000000000000 : ℝ)*(sp0) + (4012492381667729/100000000000000 : ℝ)*(sp1) + (401249277012239/10000000000000 : ℝ)*(sp2) + (386024570614061/20000000000000 : ℝ)*(sp3) + (753355459/50000000000000 : ℝ)*(sp5) + (8736377/781250000000 : ℝ)*(sp6) + (25960891/50000000000000 : ℝ)*(sp7) + (590404043/100000000000000 : ℝ)*(sp12) + (1930122904992087/100000000000000 : ℝ)*(f.failure) + (2006246944189323/50000000000000 : ℝ)*(f.sum) + (1680867135733/4461250000000000000000000000 : ℝ)*base65 + (10329670171325028349/3569000000000000000000000000000000 : ℝ)*base67 + (40638003498518971651/3569000000000000000000000000000000 : ℝ)*base70 + (28895798763171971651/3569000000000000000000000000000000 : ℝ)*base72 + (42717035117331/8922500000000000000000000000 : ℝ)*base73 + (16911157029305971651/3569000000000000000000000000000000 : ℝ)*base76 + (29014390465939971651/3569000000000000000000000000000000 : ℝ)*base78 + (10620778265264028349/3569000000000000000000000000000000 : ℝ)*base79 + (3303046746167/1115312500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (12251497/5000000000000000000000 : ℝ)*base89 + (12251497/5000000000000000000000 : ℝ)*base91 + (12251497/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79913/100000 : ℝ) ≤ (713048116605535708099169986093743/892250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (446770433/100000000000000 : ℝ)*(lower3) + (191431/160000000000 : ℝ)*(upper4) + (20783599/10000000000000 : ℝ)*(lower5) + (1646777581094337/50000000000000 : ℝ)*(major0) + (1646777581094337/50000000000000 : ℝ)*(major1) + (1646777581094337/50000000000000 : ℝ)*(major2) + (6470512859/20000000000000 : ℝ)*(sp0) + (58680153607/10000000000000 : ℝ)*(sp1) + (14187789713/4000000000000 : ℝ)*(sp2) + (210416111863/100000000000000 : ℝ)*(sp3) + (2214018942065833/50000000000000 : ℝ)*(sp8) + (4427483435159891/100000000000000 : ℝ)*(sp9) + (276732221372071/6250000000000 : ℝ)*(sp10) + (533047773579261/25000000000000 : ℝ)*(sp11) + (1066200755214453/50000000000000 : ℝ)*(f.failure) + (2214035118347981/50000000000000 : ℝ)*(f.sum) + (49187440056007/17845000000000000000000000000 : ℝ)*base65 + (2391228695196528473/1784500000000000000000000000000000 : ℝ)*base68 + (8979108740243028473/1784500000000000000000000000000000 : ℝ)*base70 + (6944350190783528473/1784500000000000000000000000000000 : ℝ)*base72 + (3000986539659/2230625000000000000000000000 : ℝ)*base73 + (16847876091022028473/1784500000000000000000000000000000 : ℝ)*base76 + (7231889721925028473/1784500000000000000000000000000000 : ℝ)*base78 + (5355627364573528473/1784500000000000000000000000000000 : ℝ)*base80 + (34787034459377/17845000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5192757/2500000000000000000000 : ℝ)*base90 + (5192757/2500000000000000000000 : ℝ)*base92 + (5192757/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-3373/4000 : ℝ) ≤ (-3009462773394163695541704651/3569000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51787119/100000000000000 : ℝ)*(lower0) + (1311577/4000000000000 : ℝ)*(upper3) + (66754157/50000000000000 : ℝ)*(lower4) + (6659837471601/200000000000 : ℝ)*(major0) + (6659837471601/200000000000 : ℝ)*(major1) + (6659837471601/200000000000 : ℝ)*(major2) + (245348777/12500000000000 : ℝ)*(sp4) + (127487492441/100000000000000 : ℝ)*(sp6) + (60861081137/100000000000000 : ℝ)*(sp7) + (152123063/6250000000000 : ℝ)*(sp8) + (4531995519962893/100000000000000 : ℝ)*(sp12) + (1132999979180529/25000000000000 : ℝ)*(sp13) + (1132968107307419/25000000000000 : ℝ)*(sp14) + (269485515758753/12500000000000 : ℝ)*(sp15) + (53898624678779/2500000000000 : ℝ)*(f.failure) + (1132999979180529/25000000000000 : ℝ)*(f.sum) + (7293421777841/713800000000000000000000000 : ℝ)*base66 + (38188652297958471/7138000000000000000000000000000 : ℝ)*base67 + (18661038899699529/7138000000000000000000000000000 : ℝ)*base70 + (198369277197962471/7138000000000000000000000000000 : ℝ)*base71 + (10676354175113/1784500000000000000000000000 : ℝ)*base74 + (11975508450694471/7138000000000000000000000000000 : ℝ)*base75 + (16737092423541529/7138000000000000000000000000000 : ℝ)*base78 + (18258950927001529/7138000000000000000000000000000 : ℝ)*base80 + (9382350470357/3569000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (1392251/125000000000000000000 : ℝ)*base90 + (1392251/125000000000000000000 : ℝ)*base92 + (1392251/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1335_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11133/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3683/6250 : ℝ) else (79913/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3373/4000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1335_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1335_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3683/6250 : ℝ) else (79913/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3373/4000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1335_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1335_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1335_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62853/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(3683/6250 : ℝ) else (79913/100000 : ℝ) ≤ X j i ∧ X j i ≤ (3373/4000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1335_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
