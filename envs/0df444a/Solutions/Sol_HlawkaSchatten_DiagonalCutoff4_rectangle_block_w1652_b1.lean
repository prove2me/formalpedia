-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1652_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:13:41.644576+00:00
-- url     : https://prove2.me/submissions/d782ace5-f6ef-471d-9bd6-eef21bbe3244

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
theorem support_rectangle_w1652_s3_0 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-320795861/2000000000 : ℝ)*x 0 + (5447008537/10000000000 : ℝ)*x 1 + (5183978797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (320795861/2000000000 : ℝ)^4927 ≤ (9923683186317/100000000000000 : ℝ)^3903 := by
    have hnat : (320795861 : ℕ)^4927*100000000000000^3903 ≤ 9923683186317^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      320795861 2000000000 9923683186317 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447008537/10000000000 : ℝ)^4927 ≤ (46444669897003/100000000000000 : ℝ)^3903 := by
    have hnat : (5447008537 : ℕ)^4927*100000000000000^3903 ≤ 46444669897003^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447008537 10000000000 46444669897003 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5183978797/10000000000 : ℝ)^4927 ≤ (10907911724087/25000000000000 : ℝ)^3903 := by
    have hnat : (5183978797 : ℕ)^4927*25000000000000^3903 ≤ 10907911724087^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183978797 10000000000 10907911724087 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-320795861/2000000000 : ℝ), (5447008537/10000000000 : ℝ), (5183978797/10000000000 : ℝ)] ![(9923683186317/100000000000000 : ℝ), (46444669897003/100000000000000 : ℝ), (10907911724087/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-320795861/2000000000 : ℝ)|^4927 ≤ (9923683186317/100000000000000 : ℝ)^3903
        have hw : |(-320795861/2000000000 : ℝ)|=(320795861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447008537/10000000000 : ℝ)|^4927 ≤ (46444669897003/100000000000000 : ℝ)^3903
        have hw : |(5447008537/10000000000 : ℝ)|=(5447008537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5183978797/10000000000 : ℝ)|^4927 ≤ (10907911724087/25000000000000 : ℝ)^3903
        have hw : |(5183978797/10000000000 : ℝ)|=(5183978797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s3_1 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069491911/2000000000 : ℝ)*x 0 + (-1739375251/10000000000 : ℝ)*x 1 + (1036795773/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069491911/2000000000 : ℝ)^4927 ≤ (2268786722347/5000000000000 : ℝ)^3903 := by
    have hnat : (1069491911 : ℕ)^4927*5000000000000^3903 ≤ 2268786722347^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069491911 2000000000 2268786722347 5000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1739375251/10000000000 : ℝ)^4927 ≤ (10992617916299/100000000000000 : ℝ)^3903 := by
    have hnat : (1739375251 : ℕ)^4927*100000000000000^3903 ≤ 10992617916299^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739375251 10000000000 10992617916299 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036795773/2000000000 : ℝ)^4927 ≤ (43631647618837/100000000000000 : ℝ)^3903 := by
    have hnat : (1036795773 : ℕ)^4927*100000000000000^3903 ≤ 43631647618837^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036795773 2000000000 43631647618837 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069491911/2000000000 : ℝ), (-1739375251/10000000000 : ℝ), (1036795773/2000000000 : ℝ)] ![(2268786722347/5000000000000 : ℝ), (10992617916299/100000000000000 : ℝ), (43631647618837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069491911/2000000000 : ℝ)|^4927 ≤ (2268786722347/5000000000000 : ℝ)^3903
        have hw : |(1069491911/2000000000 : ℝ)|=(1069491911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1739375251/10000000000 : ℝ)|^4927 ≤ (10992617916299/100000000000000 : ℝ)^3903
        have hw : |(-1739375251/10000000000 : ℝ)|=(1739375251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036795773/2000000000 : ℝ)|^4927 ≤ (43631647618837/100000000000000 : ℝ)^3903
        have hw : |(1036795773/2000000000 : ℝ)|=(1036795773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s3_2 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069491907/2000000000 : ℝ)*x 0 + (518397887/1000000000 : ℝ)*x 1 + (-1739375271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069491907/2000000000 : ℝ)^4927 ≤ (9075146846541/20000000000000 : ℝ)^3903 := by
    have hnat : (1069491907 : ℕ)^4927*20000000000000^3903 ≤ 9075146846541^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069491907 2000000000 9075146846541 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518397887/1000000000 : ℝ)^4927 ≤ (43631647671961/100000000000000 : ℝ)^3903 := by
    have hnat : (518397887 : ℕ)^4927*100000000000000^3903 ≤ 43631647671961^3903*1000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518397887 1000000000 43631647671961 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1739375271/10000000000 : ℝ)^4927 ≤ (10992618075859/100000000000000 : ℝ)^3903 := by
    have hnat : (1739375271 : ℕ)^4927*100000000000000^3903 ≤ 10992618075859^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739375271 10000000000 10992618075859 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069491907/2000000000 : ℝ), (518397887/1000000000 : ℝ), (-1739375271/10000000000 : ℝ)] ![(9075146846541/20000000000000 : ℝ), (43631647671961/100000000000000 : ℝ), (10992618075859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069491907/2000000000 : ℝ)|^4927 ≤ (9075146846541/20000000000000 : ℝ)^3903
        have hw : |(1069491907/2000000000 : ℝ)|=(1069491907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518397887/1000000000 : ℝ)|^4927 ≤ (43631647671961/100000000000000 : ℝ)^3903
        have hw : |(518397887/1000000000 : ℝ)|=(518397887/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1739375271/10000000000 : ℝ)|^4927 ≤ (10992618075859/100000000000000 : ℝ)^3903
        have hw : |(-1739375271/10000000000 : ℝ)|=(1739375271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s3_3 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4179187501/10000000000 : ℝ)*x 0 + (3848134763/10000000000 : ℝ)*x 1 + (4530373541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4179187501/10000000000 : ℝ)^4927 ≤ (33241502836991/100000000000000 : ℝ)^3903 := by
    have hnat : (4179187501 : ℕ)^4927*100000000000000^3903 ≤ 33241502836991^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4179187501 10000000000 33241502836991 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3848134763/10000000000 : ℝ)^4927 ≤ (3744084135573/12500000000000 : ℝ)^3903 := by
    have hnat : (3848134763 : ℕ)^4927*12500000000000^3903 ≤ 3744084135573^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3848134763 10000000000 3744084135573 12500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530373541/10000000000 : ℝ)^4927 ≤ (3680582405873/10000000000000 : ℝ)^3903 := by
    have hnat : (4530373541 : ℕ)^4927*10000000000000^3903 ≤ 3680582405873^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530373541 10000000000 3680582405873 10000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4179187501/10000000000 : ℝ), (3848134763/10000000000 : ℝ), (4530373541/10000000000 : ℝ)] ![(33241502836991/100000000000000 : ℝ), (3744084135573/12500000000000 : ℝ), (3680582405873/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4179187501/10000000000 : ℝ)|^4927 ≤ (33241502836991/100000000000000 : ℝ)^3903
        have hw : |(4179187501/10000000000 : ℝ)|=(4179187501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3848134763/10000000000 : ℝ)|^4927 ≤ (3744084135573/12500000000000 : ℝ)^3903
        have hw : |(3848134763/10000000000 : ℝ)|=(3848134763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530373541/10000000000 : ℝ)|^4927 ≤ (3680582405873/10000000000000 : ℝ)^3903
        have hw : |(4530373541/10000000000 : ℝ)|=(4530373541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s3_4 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-64161731/400000000 : ℝ)*x 0 + (5185972027/10000000000 : ℝ)*x 1 + (5444994409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64161731/400000000 : ℝ)^4927 ≤ (9924182802807/100000000000000 : ℝ)^3903 := by
    have hnat : (64161731 : ℕ)^4927*100000000000000^3903 ≤ 9924182802807^3903*400000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64161731 400000000 9924182802807 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5185972027/10000000000 : ℝ)^4927 ≤ (5456603214293/12500000000000 : ℝ)^3903 := by
    have hnat : (5185972027 : ℕ)^4927*12500000000000^3903 ≤ 5456603214293^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5185972027 10000000000 5456603214293 12500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444994409/10000000000 : ℝ)^4927 ≤ (23211495733313/50000000000000 : ℝ)^3903 := by
    have hnat : (5444994409 : ℕ)^4927*50000000000000^3903 ≤ 23211495733313^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444994409 10000000000 23211495733313 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-64161731/400000000 : ℝ), (5185972027/10000000000 : ℝ), (5444994409/10000000000 : ℝ)] ![(9924182802807/100000000000000 : ℝ), (5456603214293/12500000000000 : ℝ), (23211495733313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-64161731/400000000 : ℝ)|^4927 ≤ (9924182802807/100000000000000 : ℝ)^3903
        have hw : |(-64161731/400000000 : ℝ)|=(64161731/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5185972027/10000000000 : ℝ)|^4927 ≤ (5456603214293/12500000000000 : ℝ)^3903
        have hw : |(5185972027/10000000000 : ℝ)|=(5185972027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444994409/10000000000 : ℝ)|^4927 ≤ (23211495733313/50000000000000 : ℝ)^3903
        have hw : |(5444994409/10000000000 : ℝ)|=(5444994409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s3_5 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277173227/10000000000 : ℝ)*x 0 + (-1478359889/10000000000 : ℝ)*x 1 + (217799779/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277173227/10000000000 : ℝ)^4927 ≤ (4462414769273/10000000000000 : ℝ)^3903 := by
    have hnat : (5277173227 : ℕ)^4927*10000000000000^3903 ≤ 4462414769273^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277173227 10000000000 4462414769273 10000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1478359889/10000000000 : ℝ)^4927 ≤ (8952860115879/100000000000000 : ℝ)^3903 := by
    have hnat : (1478359889 : ℕ)^4927*100000000000000^3903 ≤ 8952860115879^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1478359889 10000000000 8952860115879 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217799779/400000000 : ℝ)^4927 ≤ (23211496088481/50000000000000 : ℝ)^3903 := by
    have hnat : (217799779 : ℕ)^4927*50000000000000^3903 ≤ 23211496088481^3903*400000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217799779 400000000 23211496088481 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277173227/10000000000 : ℝ), (-1478359889/10000000000 : ℝ), (217799779/400000000 : ℝ)] ![(4462414769273/10000000000000 : ℝ), (8952860115879/100000000000000 : ℝ), (23211496088481/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277173227/10000000000 : ℝ)|^4927 ≤ (4462414769273/10000000000000 : ℝ)^3903
        have hw : |(5277173227/10000000000 : ℝ)|=(5277173227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1478359889/10000000000 : ℝ)|^4927 ≤ (8952860115879/100000000000000 : ℝ)^3903
        have hw : |(-1478359889/10000000000 : ℝ)|=(1478359889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217799779/400000000 : ℝ)|^4927 ≤ (23211496088481/50000000000000 : ℝ)^3903
        have hw : |(217799779/400000000 : ℝ)|=(217799779/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s3_6 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319293431/2500000000 : ℝ)*x 0 + (5444994011/10000000000 : ℝ)*x 1 + (-184794981/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319293431/2500000000 : ℝ)^4927 ≤ (22312076499009/50000000000000 : ℝ)^3903 := by
    have hnat : (1319293431 : ℕ)^4927*50000000000000^3903 ≤ 22312076499009^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319293431 2500000000 22312076499009 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444994011/10000000000 : ℝ)^4927 ≤ (46422987183087/100000000000000 : ℝ)^3903 := by
    have hnat : (5444994011 : ℕ)^4927*100000000000000^3903 ≤ 46422987183087^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444994011 10000000000 46422987183087 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184794981/1250000000 : ℝ)^4927 ≤ (8952859802443/100000000000000 : ℝ)^3903 := by
    have hnat : (184794981 : ℕ)^4927*100000000000000^3903 ≤ 8952859802443^3903*1250000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184794981 1250000000 8952859802443 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319293431/2500000000 : ℝ), (5444994011/10000000000 : ℝ), (-184794981/1250000000 : ℝ)] ![(22312076499009/50000000000000 : ℝ), (46422987183087/100000000000000 : ℝ), (8952859802443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319293431/2500000000 : ℝ)|^4927 ≤ (22312076499009/50000000000000 : ℝ)^3903
        have hw : |(1319293431/2500000000 : ℝ)|=(1319293431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444994011/10000000000 : ℝ)|^4927 ≤ (46422987183087/100000000000000 : ℝ)^3903
        have hw : |(5444994011/10000000000 : ℝ)|=(5444994011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-184794981/1250000000 : ℝ)|^4927 ≤ (8952859802443/100000000000000 : ℝ)^3903
        have hw : |(-184794981/1250000000 : ℝ)|=(184794981/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s3_7 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2089676613/5000000000 : ℝ)*x 0 + (4525203799/10000000000 : ℝ)*x 1 + (3853359599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089676613/5000000000 : ℝ)^4927 ≤ (33243166874423/100000000000000 : ℝ)^3903 := by
    have hnat : (2089676613 : ℕ)^4927*100000000000000^3903 ≤ 33243166874423^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089676613 5000000000 33243166874423 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4525203799/10000000000 : ℝ)^4927 ≤ (7350562504749/20000000000000 : ℝ)^3903 := by
    have hnat : (4525203799 : ℕ)^4927*20000000000000^3903 ≤ 7350562504749^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4525203799 10000000000 7350562504749 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3853359599/10000000000 : ℝ)^4927 ≤ (1500201029257/5000000000000 : ℝ)^3903 := by
    have hnat : (3853359599 : ℕ)^4927*5000000000000^3903 ≤ 1500201029257^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3853359599 10000000000 1500201029257 5000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089676613/5000000000 : ℝ), (4525203799/10000000000 : ℝ), (3853359599/10000000000 : ℝ)] ![(33243166874423/100000000000000 : ℝ), (7350562504749/20000000000000 : ℝ), (1500201029257/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089676613/5000000000 : ℝ)|^4927 ≤ (33243166874423/100000000000000 : ℝ)^3903
        have hw : |(2089676613/5000000000 : ℝ)|=(2089676613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4525203799/10000000000 : ℝ)|^4927 ≤ (7350562504749/20000000000000 : ℝ)^3903
        have hw : |(4525203799/10000000000 : ℝ)|=(4525203799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3853359599/10000000000 : ℝ)|^4927 ≤ (1500201029257/5000000000000 : ℝ)^3903
        have hw : |(3853359599/10000000000 : ℝ)|=(3853359599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1652_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179688539/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10677/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16269/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16339/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16339/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10613/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16339/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16339/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10613/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16339/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16339/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10613/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10613/100000 : ℝ) ^ (4923/1024 : ℝ) ≤ (259127095976467/12500000000000000000 : ℝ) := by
    have hpowers : (10613/100000 : ℝ)^4923 ≤ (259127095976467/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10613 : ℕ)^4923*12500000000000000000^1024 ≤ 259127095976467^1024*100000^4923 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10613 100000 259127095976467 12500000000000000000 4923 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10613/100000 : ℝ)) (X := (259127095976467/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16339/100000 : ℝ) ^ (4923/1024 : ℝ) ≤ (3300040394069737/20000000000000000000 : ℝ) := by
    have hpowers : (16339/100000 : ℝ)^4923 ≤ (3300040394069737/20000000000000000000 : ℝ)^1024 := by
      have hnat : (16339 : ℕ)^4923*20000000000000000000^1024 ≤ 3300040394069737^1024*100000^4923 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16339 100000 3300040394069737 20000000000000000000 4923 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16339/100000 : ℝ)) (X := (3300040394069737/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250259127095976467/6250000000000000000 : ℝ) ≤ (1000008623742917/1000000000000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (6250259127095976467/6250000000000000000 : ℝ)^1024 ≤ (1000008623742917/1000000000000000 : ℝ)^4923 := by
      have hnat : (6250259127095976467 : ℕ)^1024*1000000000000000^4923 ≤ 1000008623742917^4923*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250259127095976467 6250000000000000000 1000008623742917 1000000000000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000008623742917/1000000000000000 : ℝ)) (X := (6250259127095976467/6250000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018573218738160421/100000000000000000000 : ℝ) ≤ (10000386300574937/10000000000000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (100018573218738160421/100000000000000000000 : ℝ)^1024 ≤ (10000386300574937/10000000000000000 : ℝ)^4923 := by
      have hnat : (100018573218738160421 : ℕ)^1024*10000000000000000^4923 ≤ 10000386300574937^4923*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018573218738160421 100000000000000000000 10000386300574937 10000000000000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000386300574937/10000000000000000 : ℝ)) (X := (100018573218738160421/100000000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003300040394069737/10000000000000000000 : ℝ) ≤ (9766295277071/9765625000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (10003300040394069737/10000000000000000000 : ℝ)^1024 ≤ (9766295277071/9765625000000 : ℝ)^4923 := by
      have hnat : (10003300040394069737 : ℕ)^1024*9765625000000^4923 ≤ 9766295277071^4923*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003300040394069737 10000000000000000000 9766295277071 9765625000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (9766295277071/9765625000000 : ℝ)) (X := (10003300040394069737/10000000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(259127095976467/12500000000000000000 : ℝ) ≤ ((4089580332513384077/4090000000000000000 : ℝ)+2*(42866163681/81800000000000 : ℝ)*(10613/100000 : ℝ))^(4923/1024 : ℝ) := by
    rw [show (4089580332513384077/4090000000000000000 : ℝ)+2*(42866163681/81800000000000 : ℝ)*(10613/100000 : ℝ)=(1000008623742917/1000000000000000 : ℝ) by norm_num, show 1+2*(259127095976467/12500000000000000000 : ℝ)=(6250259127095976467/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3300040394069737/20000000000000000000 : ℝ)+(259127095976467/12500000000000000000 : ℝ) ≤ ((4089580332513384077/4090000000000000000 : ℝ)+(42866163681/81800000000000 : ℝ)*((16339/100000 : ℝ)+(10613/100000 : ℝ)))^(4923/1024 : ℝ) := by
    rw [show (4089580332513384077/4090000000000000000 : ℝ)+(42866163681/81800000000000 : ℝ)*((16339/100000 : ℝ)+(10613/100000 : ℝ))=(10000386300574937/10000000000000000 : ℝ) by norm_num, show 1+(3300040394069737/20000000000000000000 : ℝ)+(259127095976467/12500000000000000000 : ℝ)=(100018573218738160421/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3300040394069737/20000000000000000000 : ℝ) ≤ ((4089580332513384077/4090000000000000000 : ℝ)+2*(42866163681/81800000000000 : ℝ)*(16339/100000 : ℝ))^(4923/1024 : ℝ) := by
    rw [show (4089580332513384077/4090000000000000000 : ℝ)+2*(42866163681/81800000000000 : ℝ)*(16339/100000 : ℝ)=(9766295277071/9765625000000 : ℝ) by norm_num, show 1+2*(3300040394069737/20000000000000000000 : ℝ)=(10003300040394069737/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4089580332513384077/4090000000000000000 : ℝ)*(X 1 0+X 2 0)+(42866163681/81800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (16339/100000 : ℝ)) (c := (4089580332513384077/4090000000000000000 : ℝ)) (alpha := (42866163681/81800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4089580332513384077/4090000000000000000 : ℝ)*(X 0 1+X 2 1)+(42866163681/81800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (16339/100000 : ℝ)) (c := (4089580332513384077/4090000000000000000 : ℝ)) (alpha := (42866163681/81800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4089580332513384077/4090000000000000000 : ℝ)*(X 0 2+X 1 2)+(42866163681/81800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10613/100000 : ℝ)) (hi := (16339/100000 : ℝ)) (c := (4089580332513384077/4090000000000000000 : ℝ)) (alpha := (42866163681/81800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-320795861/2000000000 : ℝ)*X 0 0+(5447008537/10000000000 : ℝ)*X 0 1+(5183978797/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069491911/2000000000 : ℝ)*X 1 0+(-1739375251/10000000000 : ℝ)*X 1 1+(1036795773/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069491907/2000000000 : ℝ)*X 2 0+(518397887/1000000000 : ℝ)*X 2 1+(-1739375271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4179187501/10000000000 : ℝ)*X 0 0+(3848134763/10000000000 : ℝ)*X 0 1+(4530373541/10000000000 : ℝ)*X 0 2+(4179187501/10000000000 : ℝ)*X 1 0+(3848134763/10000000000 : ℝ)*X 1 1+(4530373541/10000000000 : ℝ)*X 1 2+(4179187501/10000000000 : ℝ)*X 2 0+(3848134763/10000000000 : ℝ)*X 2 1+(4530373541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-64161731/400000000 : ℝ)*X 0 0+(5185972027/10000000000 : ℝ)*X 0 1+(5444994409/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277173227/10000000000 : ℝ)*X 1 0+(-1478359889/10000000000 : ℝ)*X 1 1+(217799779/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1319293431/2500000000 : ℝ)*X 2 0+(5444994011/10000000000 : ℝ)*X 2 1+(-184794981/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2089676613/5000000000 : ℝ)*X 0 0+(4525203799/10000000000 : ℝ)*X 0 1+(3853359599/10000000000 : ℝ)*X 0 2+(2089676613/5000000000 : ℝ)*X 1 0+(4525203799/10000000000 : ℝ)*X 1 1+(3853359599/10000000000 : ℝ)*X 1 2+(2089676613/5000000000 : ℝ)*X 2 0+(4525203799/10000000000 : ℝ)*X 2 1+(3853359599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (84259280785362761244444579/25562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (741664451/100000000000000 : ℝ)*(base19) + (643205557/100000000000000 : ℝ)*(base23) + (45046753/100000000000000 : ℝ)*(lower2) + (136245873/100000000000000 : ℝ)*(upper3) + (28997357/50000000000000 : ℝ)*(upper5) + (658455205777009/25000000000000 : ℝ)*(major0) + (658455205777009/25000000000000 : ℝ)*(major1) + (658455205777009/25000000000000 : ℝ)*(major2) + (3801862011629367/100000000000000 : ℝ)*(sp0) + (3801870725108943/100000000000000 : ℝ)*(sp1) + (3801870823567837/100000000000000 : ℝ)*(sp2) + (366441462008467/25000000000000 : ℝ)*(sp3) + (9455144027/100000000000000 : ℝ)*(sp4) + (4221535253/100000000000000 : ℝ)*(sp7) + (1465770069569121/100000000000000 : ℝ)*(f.failure) + (1900935733386697/50000000000000 : ℝ)*(f.sum) + (1964781631903/511250000000000000000000000 : ℝ)*base66 + (204487821598014307/102250000000000000000000000000000 : ℝ)*base68 + (548332939383514307/102250000000000000000000000000000 : ℝ)*base70 + (233301466314985693/102250000000000000000000000000000 : ℝ)*base71 + (33415354593/31953125000000000000000000 : ℝ)*base74 + (147432484277764307/102250000000000000000000000000000 : ℝ)*base76 + (484869346402514307/102250000000000000000000000000000 : ℝ)*base78 + (655672631907514307/102250000000000000000000000000000 : ℝ)*base80 + (3994576947699/1022500000000000000000000000 : ℝ)*base81 + (112004219/10000000000000000000000 : ℝ)*base89 + (112004219/10000000000000000000000 : ℝ)*base91 + (112004219/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2661883880227244135725231743/204500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (103628857/6250000000000 : ℝ)*(base19) + (1086814847/50000000000000 : ℝ)*(base23) + (38709003/20000000000000 : ℝ)*(upper3) + (13577351/20000000000000 : ℝ)*(lower4) + (252230663/100000000000000 : ℝ)*(upper5) + (2674556344797149/100000000000000 : ℝ)*(major0) + (2674556344797149/100000000000000 : ℝ)*(major1) + (2674556344797149/100000000000000 : ℝ)*(major2) + (11248052307/50000000000000 : ℝ)*(sp1) + (757749681/3125000000000 : ℝ)*(sp2) + (965168028462433/25000000000000 : ℝ)*(sp4) + (1930323979841703/50000000000000 : ℝ)*(sp5) + (1930322846115123/50000000000000 : ℝ)*(sp6) + (1488440141859659/100000000000000 : ℝ)*(sp7) + (1488440141859659/100000000000000 : ℝ)*(f.failure) + (965168028462433/25000000000000 : ℝ)*(f.sum) + (7846772577591/4090000000000000000000000000 : ℝ)*base66 + (655674609620046473/409000000000000000000000000000000 : ℝ)*base67 + (2097860215604046473/409000000000000000000000000000000 : ℝ)*base69 + (583045796171046473/409000000000000000000000000000000 : ℝ)*base71 + (11547693069099/4090000000000000000000000000 : ℝ)*base73 + (2090491437656046473/409000000000000000000000000000000 : ℝ)*base75 + (988338255343046473/409000000000000000000000000000000 : ℝ)*base77 + (257592871982046473/409000000000000000000000000000000 : ℝ)*base79 + (11417279296379/4090000000000000000000000000 : ℝ)*base81 + (31251799/10000000000000000000000 : ℝ)*base90 + (31251799/10000000000000000000000 : ℝ)*base92 + (31251799/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1652_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179688539/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16269/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1652_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1652_s4_0 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-401005317/2500000000 : ℝ)*x 0 + (5446790297/10000000000 : ℝ)*x 1 + (2592084521/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401005317/2500000000 : ℝ)^4927 ≤ (1984802184767/20000000000000 : ℝ)^3903 := by
    have hnat : (401005317 : ℕ)^4927*20000000000000^3903 ≤ 1984802184767^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401005317 2500000000 1984802184767 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5446790297/10000000000 : ℝ)^4927 ≤ (9288464167621/20000000000000 : ℝ)^3903 := by
    have hnat : (5446790297 : ℕ)^4927*20000000000000^3903 ≤ 9288464167621^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5446790297 10000000000 9288464167621 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2592084521/5000000000 : ℝ)^4927 ≤ (10908417057193/25000000000000 : ℝ)^3903 := by
    have hnat : (2592084521 : ℕ)^4927*25000000000000^3903 ≤ 10908417057193^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592084521 5000000000 10908417057193 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-401005317/2500000000 : ℝ), (5446790297/10000000000 : ℝ), (2592084521/5000000000 : ℝ)] ![(1984802184767/20000000000000 : ℝ), (9288464167621/20000000000000 : ℝ), (10908417057193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-401005317/2500000000 : ℝ)|^4927 ≤ (1984802184767/20000000000000 : ℝ)^3903
        have hw : |(-401005317/2500000000 : ℝ)|=(401005317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5446790297/10000000000 : ℝ)|^4927 ≤ (9288464167621/20000000000000 : ℝ)^3903
        have hw : |(5446790297/10000000000 : ℝ)|=(5446790297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2592084521/5000000000 : ℝ)|^4927 ≤ (10908417057193/25000000000000 : ℝ)^3903
        have hw : |(2592084521/5000000000 : ℝ)|=(2592084521/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s4_1 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334212539/625000000 : ℝ)*x 0 + (-869600537/5000000000 : ℝ)*x 1 + (5184169061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334212539/625000000 : ℝ)^4927 ≤ (45375103194089/100000000000000 : ℝ)^3903 := by
    have hnat : (334212539 : ℕ)^4927*100000000000000^3903 ≤ 45375103194089^3903*625000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334212539 625000000 45375103194089 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (869600537/5000000000 : ℝ)^4927 ≤ (2198245671481/20000000000000 : ℝ)^3903 := by
    have hnat : (869600537 : ℕ)^4927*20000000000000^3903 ≤ 2198245671481^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869600537 5000000000 2198245671481 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184169061/10000000000 : ℝ)^4927 ≤ (21816834215323/50000000000000 : ℝ)^3903 := by
    have hnat : (5184169061 : ℕ)^4927*50000000000000^3903 ≤ 21816834215323^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184169061 10000000000 21816834215323 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334212539/625000000 : ℝ), (-869600537/5000000000 : ℝ), (5184169061/10000000000 : ℝ)] ![(45375103194089/100000000000000 : ℝ), (2198245671481/20000000000000 : ℝ), (21816834215323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334212539/625000000 : ℝ)|^4927 ≤ (45375103194089/100000000000000 : ℝ)^3903
        have hw : |(334212539/625000000 : ℝ)|=(334212539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-869600537/5000000000 : ℝ)|^4927 ≤ (2198245671481/20000000000000 : ℝ)^3903
        have hw : |(-869600537/5000000000 : ℝ)|=(869600537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184169061/10000000000 : ℝ)|^4927 ≤ (21816834215323/50000000000000 : ℝ)^3903
        have hw : |(5184169061/10000000000 : ℝ)|=(5184169061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s4_2 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8555841/16000000 : ℝ)*x 0 + (1296042263/2500000000 : ℝ)*x 1 + (-347840217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8555841/16000000 : ℝ)^4927 ≤ (45375103204801/100000000000000 : ℝ)^3903 := by
    have hnat : (8555841 : ℕ)^4927*100000000000000^3903 ≤ 45375103204801^3903*16000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8555841 16000000 45375103204801 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296042263/2500000000 : ℝ)^4927 ≤ (21816834167511/50000000000000 : ℝ)^3903 := by
    have hnat : (1296042263 : ℕ)^4927*50000000000000^3903 ≤ 21816834167511^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296042263 2500000000 21816834167511 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347840217/2000000000 : ℝ)^4927 ≤ (274780711129/2500000000000 : ℝ)^3903 := by
    have hnat : (347840217 : ℕ)^4927*2500000000000^3903 ≤ 274780711129^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347840217 2000000000 274780711129 2500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8555841/16000000 : ℝ), (1296042263/2500000000 : ℝ), (-347840217/2000000000 : ℝ)] ![(45375103204801/100000000000000 : ℝ), (21816834167511/50000000000000 : ℝ), (274780711129/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8555841/16000000 : ℝ)|^4927 ≤ (45375103204801/100000000000000 : ℝ)^3903
        have hw : |(8555841/16000000 : ℝ)|=(8555841/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296042263/2500000000 : ℝ)|^4927 ≤ (21816834167511/50000000000000 : ℝ)^3903
        have hw : |(1296042263/2500000000 : ℝ)|=(1296042263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-347840217/2000000000 : ℝ)|^4927 ≤ (274780711129/2500000000000 : ℝ)^3903
        have hw : |(-347840217/2000000000 : ℝ)|=(347840217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s4_3 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2089607787/5000000000 : ℝ)*x 0 + (962165449/2500000000 : ℝ)*x 1 + (2264920549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089607787/5000000000 : ℝ)^4927 ≤ (33241784715531/100000000000000 : ℝ)^3903 := by
    have hnat : (2089607787 : ℕ)^4927*100000000000000^3903 ≤ 33241784715531^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089607787 5000000000 33241784715531 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (962165449/2500000000 : ℝ)^4927 ≤ (29957851715221/100000000000000 : ℝ)^3903 := by
    have hnat : (962165449 : ℕ)^4927*100000000000000^3903 ≤ 29957851715221^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962165449 2500000000 29957851715221 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264920549/5000000000 : ℝ)^4927 ≤ (36800363551703/100000000000000 : ℝ)^3903 := by
    have hnat : (2264920549 : ℕ)^4927*100000000000000^3903 ≤ 36800363551703^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264920549 5000000000 36800363551703 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089607787/5000000000 : ℝ), (962165449/2500000000 : ℝ), (2264920549/5000000000 : ℝ)] ![(33241784715531/100000000000000 : ℝ), (29957851715221/100000000000000 : ℝ), (36800363551703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089607787/5000000000 : ℝ)|^4927 ≤ (33241784715531/100000000000000 : ℝ)^3903
        have hw : |(2089607787/5000000000 : ℝ)|=(2089607787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(962165449/2500000000 : ℝ)|^4927 ≤ (29957851715221/100000000000000 : ℝ)^3903
        have hw : |(962165449/2500000000 : ℝ)|=(962165449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264920549/5000000000 : ℝ)|^4927 ≤ (36800363551703/100000000000000 : ℝ)^3903
        have hw : |(2264920549/5000000000 : ℝ)|=(2264920549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s4_4 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-802042539/5000000000 : ℝ)*x 0 + (1296539021/2500000000 : ℝ)*x 1 + (5444782353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (802042539/5000000000 : ℝ)^4927 ≤ (9924509294113/100000000000000 : ℝ)^3903 := by
    have hnat : (802042539 : ℕ)^4927*100000000000000^3903 ≤ 9924509294113^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802042539 5000000000 9924509294113 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296539021/2500000000 : ℝ)^4927 ≤ (43654781496879/100000000000000 : ℝ)^3903 := by
    have hnat : (1296539021 : ℕ)^4927*100000000000000^3903 ≤ 43654781496879^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296539021 2500000000 43654781496879 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444782353/10000000000 : ℝ)^4927 ≤ (1450647162227/3125000000000 : ℝ)^3903 := by
    have hnat : (5444782353 : ℕ)^4927*3125000000000^3903 ≤ 1450647162227^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444782353 10000000000 1450647162227 3125000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-802042539/5000000000 : ℝ), (1296539021/2500000000 : ℝ), (5444782353/10000000000 : ℝ)] ![(9924509294113/100000000000000 : ℝ), (43654781496879/100000000000000 : ℝ), (1450647162227/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-802042539/5000000000 : ℝ)|^4927 ≤ (9924509294113/100000000000000 : ℝ)^3903
        have hw : |(-802042539/5000000000 : ℝ)|=(802042539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296539021/2500000000 : ℝ)|^4927 ≤ (43654781496879/100000000000000 : ℝ)^3903
        have hw : |(1296539021/2500000000 : ℝ)|=(1296539021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444782353/10000000000 : ℝ)|^4927 ≤ (1450647162227/3125000000000 : ℝ)^3903
        have hw : |(5444782353/10000000000 : ℝ)|=(5444782353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s4_5 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5277223879/10000000000 : ℝ)*x 0 + (-147858779/1000000000 : ℝ)*x 1 + (5444782353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5277223879/10000000000 : ℝ)^4927 ≤ (11156172096119/25000000000000 : ℝ)^3903 := by
    have hnat : (5277223879 : ℕ)^4927*25000000000000^3903 ≤ 11156172096119^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5277223879 10000000000 11156172096119 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147858779/1000000000 : ℝ)^4927 ≤ (1790920481343/20000000000000 : ℝ)^3903 := by
    have hnat : (147858779 : ℕ)^4927*20000000000000^3903 ≤ 1790920481343^3903*1000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147858779 1000000000 1790920481343 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5444782353/10000000000 : ℝ)^4927 ≤ (1450647162227/3125000000000 : ℝ)^3903 := by
    have hnat : (5444782353 : ℕ)^4927*3125000000000^3903 ≤ 1450647162227^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444782353 10000000000 1450647162227 3125000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5277223879/10000000000 : ℝ), (-147858779/1000000000 : ℝ), (5444782353/10000000000 : ℝ)] ![(11156172096119/25000000000000 : ℝ), (1790920481343/20000000000000 : ℝ), (1450647162227/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5277223879/10000000000 : ℝ)|^4927 ≤ (11156172096119/25000000000000 : ℝ)^3903
        have hw : |(5277223879/10000000000 : ℝ)|=(5277223879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-147858779/1000000000 : ℝ)|^4927 ≤ (1790920481343/20000000000000 : ℝ)^3903
        have hw : |(-147858779/1000000000 : ℝ)|=(147858779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5444782353/10000000000 : ℝ)|^4927 ≤ (1450647162227/3125000000000 : ℝ)^3903
        have hw : |(5444782353/10000000000 : ℝ)|=(5444782353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s4_6 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638611939/5000000000 : ℝ)*x 0 + (2722391177/5000000000 : ℝ)*x 1 + (-147858779/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638611939/5000000000 : ℝ)^4927 ≤ (44624688373801/100000000000000 : ℝ)^3903 := by
    have hnat : (2638611939 : ℕ)^4927*100000000000000^3903 ≤ 44624688373801^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638611939 5000000000 44624688373801 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2722391177/5000000000 : ℝ)^4927 ≤ (46420709202027/100000000000000 : ℝ)^3903 := by
    have hnat : (2722391177 : ℕ)^4927*100000000000000^3903 ≤ 46420709202027^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2722391177 5000000000 46420709202027 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147858779/1000000000 : ℝ)^4927 ≤ (1790920481343/20000000000000 : ℝ)^3903 := by
    have hnat : (147858779 : ℕ)^4927*20000000000000^3903 ≤ 1790920481343^3903*1000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147858779 1000000000 1790920481343 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638611939/5000000000 : ℝ), (2722391177/5000000000 : ℝ), (-147858779/1000000000 : ℝ)] ![(44624688373801/100000000000000 : ℝ), (46420709202027/100000000000000 : ℝ), (1790920481343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638611939/5000000000 : ℝ)|^4927 ≤ (44624688373801/100000000000000 : ℝ)^3903
        have hw : |(2638611939/5000000000 : ℝ)|=(2638611939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2722391177/5000000000 : ℝ)|^4927 ≤ (46420709202027/100000000000000 : ℝ)^3903
        have hw : |(2722391177/5000000000 : ℝ)|=(2722391177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-147858779/1000000000 : ℝ)|^4927 ≤ (1790920481343/20000000000000 : ℝ)^3903
        have hw : |(-147858779/1000000000 : ℝ)|=(147858779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_s4_7 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835876227/2000000000 : ℝ)*x 0 + (4524687191/10000000000 : ℝ)*x 1 + (385386993/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835876227/2000000000 : ℝ)^4927 ≤ (33243447109167/100000000000000 : ℝ)^3903 := by
    have hnat : (835876227 : ℕ)^4927*100000000000000^3903 ≤ 33243447109167^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835876227 2000000000 33243447109167 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524687191/10000000000 : ℝ)^4927 ≤ (9186878999553/25000000000000 : ℝ)^3903 := by
    have hnat : (4524687191 : ℕ)^4927*25000000000000^3903 ≤ 9186878999553^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524687191 10000000000 9186878999553 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (385386993/1000000000 : ℝ)^4927 ≤ (7502259221053/25000000000000 : ℝ)^3903 := by
    have hnat : (385386993 : ℕ)^4927*25000000000000^3903 ≤ 7502259221053^3903*1000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385386993 1000000000 7502259221053 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835876227/2000000000 : ℝ), (4524687191/10000000000 : ℝ), (385386993/1000000000 : ℝ)] ![(33243447109167/100000000000000 : ℝ), (9186878999553/25000000000000 : ℝ), (7502259221053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835876227/2000000000 : ℝ)|^4927 ≤ (33243447109167/100000000000000 : ℝ)^3903
        have hw : |(835876227/2000000000 : ℝ)|=(835876227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524687191/10000000000 : ℝ)|^4927 ≤ (9186878999553/25000000000000 : ℝ)^3903
        have hw : |(4524687191/10000000000 : ℝ)|=(4524687191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(385386993/1000000000 : ℝ)|^4927 ≤ (7502259221053/25000000000000 : ℝ)^3903
        have hw : |(385386993/1000000000 : ℝ)|=(385386993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1652_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179688539/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16269/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10681/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2033/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16269/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10677/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16269/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10677/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16269/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10677/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16269/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10677/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16269/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10677/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16269/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10677/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10677/100000 : ℝ) ^ (4923/1024 : ℝ) ≤ (426762132354607/20000000000000000000 : ℝ) := by
    have hpowers : (10677/100000 : ℝ)^4923 ≤ (426762132354607/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10677 : ℕ)^4923*20000000000000000000^1024 ≤ 426762132354607^1024*100000^4923 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10677 100000 426762132354607 20000000000000000000 4923 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10677/100000 : ℝ)) (X := (426762132354607/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16269/100000 : ℝ) ^ (4923/1024 : ℝ) ≤ (16163109373035887/100000000000000000000 : ℝ) := by
    have hpowers : (16269/100000 : ℝ)^4923 ≤ (16163109373035887/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16269 : ℕ)^4923*100000000000000000000^1024 ≤ 16163109373035887^1024*100000^4923 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16269 100000 16163109373035887 100000000000000000000 4923 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16269/100000 : ℝ)) (X := (16163109373035887/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000426762132354607/10000000000000000000 : ℝ) ≤ (2000017753282083/2000000000000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (10000426762132354607/10000000000000000000 : ℝ)^1024 ≤ (2000017753282083/2000000000000000 : ℝ)^4923 := by
      have hnat : (10000426762132354607 : ℕ)^1024*2000000000000000^4923 ≤ 2000017753282083^4923*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000426762132354607 10000000000000000000 2000017753282083 2000000000000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000017753282083/2000000000000000 : ℝ)) (X := (10000426762132354607/10000000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50009148460017404461/50000000000000000000 : ℝ) ≤ (10000380554311077/10000000000000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (50009148460017404461/50000000000000000000 : ℝ)^1024 ≤ (10000380554311077/10000000000000000 : ℝ)^4923 := by
      have hnat : (50009148460017404461 : ℕ)^1024*10000000000000000^4923 ≤ 10000380554311077^4923*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009148460017404461 50000000000000000000 10000380554311077 10000000000000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000380554311077/10000000000000000 : ℝ)) (X := (50009148460017404461/50000000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50016163109373035887/50000000000000000000 : ℝ) ≤ (10000672342211739/10000000000000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (50016163109373035887/50000000000000000000 : ℝ)^1024 ≤ (10000672342211739/10000000000000000 : ℝ)^4923 := by
      have hnat : (50016163109373035887 : ℕ)^1024*10000000000000000^4923 ≤ 10000672342211739^4923*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50016163109373035887 50000000000000000000 10000672342211739 10000000000000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000672342211739/10000000000000000 : ℝ)) (X := (50016163109373035887/50000000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(426762132354607/20000000000000000000 : ℝ) ≤ ((4659522128578025361/4660000000000000000 : ℝ)+2*(48631316777/93200000000000 : ℝ)*(10677/100000 : ℝ))^(4923/1024 : ℝ) := by
    rw [show (4659522128578025361/4660000000000000000 : ℝ)+2*(48631316777/93200000000000 : ℝ)*(10677/100000 : ℝ)=(2000017753282083/2000000000000000 : ℝ) by norm_num, show 1+2*(426762132354607/20000000000000000000 : ℝ)=(10000426762132354607/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16163109373035887/100000000000000000000 : ℝ)+(426762132354607/20000000000000000000 : ℝ) ≤ ((4659522128578025361/4660000000000000000 : ℝ)+(48631316777/93200000000000 : ℝ)*((16269/100000 : ℝ)+(10677/100000 : ℝ)))^(4923/1024 : ℝ) := by
    rw [show (4659522128578025361/4660000000000000000 : ℝ)+(48631316777/93200000000000 : ℝ)*((16269/100000 : ℝ)+(10677/100000 : ℝ))=(10000380554311077/10000000000000000 : ℝ) by norm_num, show 1+(16163109373035887/100000000000000000000 : ℝ)+(426762132354607/20000000000000000000 : ℝ)=(50009148460017404461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16163109373035887/100000000000000000000 : ℝ) ≤ ((4659522128578025361/4660000000000000000 : ℝ)+2*(48631316777/93200000000000 : ℝ)*(16269/100000 : ℝ))^(4923/1024 : ℝ) := by
    rw [show (4659522128578025361/4660000000000000000 : ℝ)+2*(48631316777/93200000000000 : ℝ)*(16269/100000 : ℝ)=(10000672342211739/10000000000000000 : ℝ) by norm_num, show 1+2*(16163109373035887/100000000000000000000 : ℝ)=(50016163109373035887/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4659522128578025361/4660000000000000000 : ℝ)*(X 1 0+X 2 0)+(48631316777/93200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10677/100000 : ℝ)) (hi := (16269/100000 : ℝ)) (c := (4659522128578025361/4660000000000000000 : ℝ)) (alpha := (48631316777/93200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4659522128578025361/4660000000000000000 : ℝ)*(X 0 1+X 2 1)+(48631316777/93200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10677/100000 : ℝ)) (hi := (16269/100000 : ℝ)) (c := (4659522128578025361/4660000000000000000 : ℝ)) (alpha := (48631316777/93200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4659522128578025361/4660000000000000000 : ℝ)*(X 0 2+X 1 2)+(48631316777/93200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10677/100000 : ℝ)) (hi := (16269/100000 : ℝ)) (c := (4659522128578025361/4660000000000000000 : ℝ)) (alpha := (48631316777/93200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-401005317/2500000000 : ℝ)*X 0 0+(5446790297/10000000000 : ℝ)*X 0 1+(2592084521/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334212539/625000000 : ℝ)*X 1 0+(-869600537/5000000000 : ℝ)*X 1 1+(5184169061/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((8555841/16000000 : ℝ)*X 2 0+(1296042263/2500000000 : ℝ)*X 2 1+(-347840217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2089607787/5000000000 : ℝ)*X 0 0+(962165449/2500000000 : ℝ)*X 0 1+(2264920549/5000000000 : ℝ)*X 0 2+(2089607787/5000000000 : ℝ)*X 1 0+(962165449/2500000000 : ℝ)*X 1 1+(2264920549/5000000000 : ℝ)*X 1 2+(2089607787/5000000000 : ℝ)*X 2 0+(962165449/2500000000 : ℝ)*X 2 1+(2264920549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-802042539/5000000000 : ℝ)*X 0 0+(1296539021/2500000000 : ℝ)*X 0 1+(5444782353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5277223879/10000000000 : ℝ)*X 1 0+(-147858779/1000000000 : ℝ)*X 1 1+(5444782353/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638611939/5000000000 : ℝ)*X 2 0+(2722391177/5000000000 : ℝ)*X 2 1+(-147858779/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((835876227/2000000000 : ℝ)*X 0 0+(4524687191/10000000000 : ℝ)*X 0 1+(385386993/1000000000 : ℝ)*X 0 2+(835876227/2000000000 : ℝ)*X 1 0+(4524687191/10000000000 : ℝ)*X 1 1+(385386993/1000000000 : ℝ)*X 1 2+(835876227/2000000000 : ℝ)*X 2 0+(4524687191/10000000000 : ℝ)*X 2 1+(385386993/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (280667795483104925882403453/58250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (768785063/100000000000000 : ℝ)*(base19) + (18351667/2500000000000 : ℝ)*(base23) + (18946089/100000000000000 : ℝ)*(lower2) + (118690437/100000000000000 : ℝ)*(upper3) + (42415583/50000000000000 : ℝ)*(upper5) + (1318958836339609/50000000000000 : ℝ)*(major0) + (1318958836339609/50000000000000 : ℝ)*(major1) + (1318958836339609/50000000000000 : ℝ)*(major2) + (3807775212926761/100000000000000 : ℝ)*(sp0) + (380778437372829/10000000000000 : ℝ)*(sp1) + (1903892204223337/50000000000000 : ℝ)*(sp2) + (367011486259513/25000000000000 : ℝ)*(sp3) + (310299581/3125000000000 : ℝ)*(sp4) + (4097195981/100000000000000 : ℝ)*(sp7) + (734025021117017/50000000000000 : ℝ)*(f.failure) + (3807785142513353/100000000000000 : ℝ)*(f.sum) + (11762946659723/2330000000000000000000000000 : ℝ)*base65 + (1096720510056473849/233000000000000000000000000000000 : ℝ)*base67 + (1460374827608473849/233000000000000000000000000000000 : ℝ)*base69 + (1801641334801473849/233000000000000000000000000000000 : ℝ)*base71 + (4376743804203/2330000000000000000000000000 : ℝ)*base73 + (1240914049392473849/233000000000000000000000000000000 : ℝ)*base75 + (1178525173231473849/233000000000000000000000000000000 : ℝ)*base77 + (825778637542526151/233000000000000000000000000000000 : ℝ)*base80 + (14542734573313/2330000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (32768163/5000000000000000000000 : ℝ)*base89 + (32768163/5000000000000000000000 : ℝ)*base91 + (32768163/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9193766020448725675587/1165000000000000000000000000 : ℝ) := by norm_num
    linear_combination (289248827/25000000000000 : ℝ)*(base19) + (250381097/20000000000000 : ℝ)*(base23) + (361788659/100000000000000 : ℝ)*(lower1) + (82623941/50000000000000 : ℝ)*(upper3) + (8618887/20000000000000 : ℝ)*(lower4) + (163158089/100000000000000 : ℝ)*(upper5) + (669660275192069/25000000000000 : ℝ)*(major0) + (669660275192069/25000000000000 : ℝ)*(major1) + (669660275192069/25000000000000 : ℝ)*(major2) + (525704433/50000000000000 : ℝ)*(sp2) + (1933284277134783/50000000000000 : ℝ)*(sp4) + (1933283698637129/50000000000000 : ℝ)*(sp5) + (241660390684701/6250000000000 : ℝ)*(sp6) + (745356692106077/50000000000000 : ℝ)*(sp7) + (745356692106077/50000000000000 : ℝ)*(f.failure) + (1933284277134783/50000000000000 : ℝ)*(f.sum) + (5480226076317/1165000000000000000000000000 : ℝ)*base66 + (3387734029498288091/116500000000000000000000000000000 : ℝ)*base68 + (507229220011711909/116500000000000000000000000000000 : ℝ)*base69 + (920003374029288091/116500000000000000000000000000000 : ℝ)*base72 + (3633737135397/1165000000000000000000000000 : ℝ)*base74 + (3511764512142288091/116500000000000000000000000000000 : ℝ)*base76 + (299380909456711909/116500000000000000000000000000000 : ℝ)*base77 + (579121965093711909/116500000000000000000000000000000 : ℝ)*base79 + (4368487928437/1165000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (9151503/5000000000000000000000 : ℝ)*base89 + (9151503/5000000000000000000000 : ℝ)*base91 + (9151503/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1652_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179688539/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16269/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10677/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10681/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2033/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1652_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1652_box_0 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-269351217/2000000000 : ℝ)*x 0 + (5407573171/10000000000 : ℝ)*x 1 + (270378663/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269351217/2000000000 : ℝ)^4927 ≤ (1591758582551/20000000000000 : ℝ)^3903 := by
    have hnat : (269351217 : ℕ)^4927*20000000000000^3903 ≤ 1591758582551^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269351217 2000000000 1591758582551 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407573171/10000000000 : ℝ)^4927 ≤ (23010301527261/50000000000000 : ℝ)^3903 := by
    have hnat : (5407573171 : ℕ)^4927*50000000000000^3903 ≤ 23010301527261^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407573171 10000000000 23010301527261 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270378663/500000000 : ℝ)^4927 ≤ (11505151002667/25000000000000 : ℝ)^3903 := by
    have hnat : (270378663 : ℕ)^4927*25000000000000^3903 ≤ 11505151002667^3903*500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270378663 500000000 11505151002667 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-269351217/2000000000 : ℝ), (5407573171/10000000000 : ℝ), (270378663/500000000 : ℝ)] ![(1591758582551/20000000000000 : ℝ), (23010301527261/50000000000000 : ℝ), (11505151002667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-269351217/2000000000 : ℝ)|^4927 ≤ (1591758582551/20000000000000 : ℝ)^3903
        have hw : |(-269351217/2000000000 : ℝ)|=(269351217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407573171/10000000000 : ℝ)|^4927 ≤ (23010301527261/50000000000000 : ℝ)^3903
        have hw : |(5407573171/10000000000 : ℝ)|=(5407573171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270378663/500000000 : ℝ)|^4927 ≤ (11505151002667/25000000000000 : ℝ)^3903
        have hw : |(270378663/500000000 : ℝ)|=(270378663/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_1 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251052099/10000000000 : ℝ)*x 0 + (-156676171/1000000000 : ℝ)*x 1 + (2703786693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251052099/10000000000 : ℝ)^4927 ≤ (5543186967707/12500000000000 : ℝ)^3903 := by
    have hnat : (5251052099 : ℕ)^4927*12500000000000^3903 ≤ 5543186967707^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251052099 10000000000 5543186967707 12500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156676171/1000000000 : ℝ)^4927 ≤ (9633898875561/100000000000000 : ℝ)^3903 := by
    have hnat : (156676171 : ℕ)^4927*100000000000000^3903 ≤ 9633898875561^3903*1000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156676171 1000000000 9633898875561 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703786693/5000000000 : ℝ)^4927 ≤ (5752575670539/12500000000000 : ℝ)^3903 := by
    have hnat : (2703786693 : ℕ)^4927*12500000000000^3903 ≤ 5752575670539^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703786693 5000000000 5752575670539 12500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251052099/10000000000 : ℝ), (-156676171/1000000000 : ℝ), (2703786693/5000000000 : ℝ)] ![(5543186967707/12500000000000 : ℝ), (9633898875561/100000000000000 : ℝ), (5752575670539/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251052099/10000000000 : ℝ)|^4927 ≤ (5543186967707/12500000000000 : ℝ)^3903
        have hw : |(5251052099/10000000000 : ℝ)|=(5251052099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-156676171/1000000000 : ℝ)|^4927 ≤ (9633898875561/100000000000000 : ℝ)^3903
        have hw : |(-156676171/1000000000 : ℝ)|=(156676171/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703786693/5000000000 : ℝ)|^4927 ≤ (5752575670539/12500000000000 : ℝ)^3903
        have hw : |(2703786693/5000000000 : ℝ)|=(2703786693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_2 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2625525991/5000000000 : ℝ)*x 0 + (5407573373/10000000000 : ℝ)*x 1 + (-1566761889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2625525991/5000000000 : ℝ)^4927 ≤ (886909889887/2000000000000 : ℝ)^3903 := by
    have hnat : (2625525991 : ℕ)^4927*2000000000000^3903 ≤ 886909889887^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2625525991 5000000000 886909889887 2000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407573373/10000000000 : ℝ)^4927 ≤ (920412104493/2000000000000 : ℝ)^3903 := by
    have hnat : (5407573373 : ℕ)^4927*2000000000000^3903 ≤ 920412104493^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407573373 10000000000 920412104493 2000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1566761889/10000000000 : ℝ)^4927 ≤ (9633900264989/100000000000000 : ℝ)^3903 := by
    have hnat : (1566761889 : ℕ)^4927*100000000000000^3903 ≤ 9633900264989^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1566761889 10000000000 9633900264989 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2625525991/5000000000 : ℝ), (5407573373/10000000000 : ℝ), (-1566761889/10000000000 : ℝ)] ![(886909889887/2000000000000 : ℝ), (920412104493/2000000000000 : ℝ), (9633900264989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2625525991/5000000000 : ℝ)|^4927 ≤ (886909889887/2000000000000 : ℝ)^3903
        have hw : |(2625525991/5000000000 : ℝ)|=(2625525991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407573373/10000000000 : ℝ)|^4927 ≤ (920412104493/2000000000000 : ℝ)^3903
        have hw : |(5407573373/10000000000 : ℝ)|=(5407573373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1566761889/10000000000 : ℝ)|^4927 ≤ (9633900264989/100000000000000 : ℝ)^3903
        have hw : |(-1566761889/10000000000 : ℝ)|=(1566761889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_3 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (891176759/2000000000 : ℝ)*x 0 + (4052870933/10000000000 : ℝ)*x 1 + (50660879/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891176759/2000000000 : ℝ)^4927 ≤ (36043531877101/100000000000000 : ℝ)^3903 := by
    have hnat : (891176759 : ℕ)^4927*100000000000000^3903 ≤ 36043531877101^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891176759 2000000000 36043531877101 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4052870933/10000000000 : ℝ)^4927 ≤ (15989118553397/50000000000000 : ℝ)^3903 := by
    have hnat : (4052870933 : ℕ)^4927*50000000000000^3903 ≤ 15989118553397^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4052870933 10000000000 15989118553397 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50660879/125000000 : ℝ)^4927 ≤ (7994557750271/25000000000000 : ℝ)^3903 := by
    have hnat : (50660879 : ℕ)^4927*25000000000000^3903 ≤ 7994557750271^3903*125000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50660879 125000000 7994557750271 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(891176759/2000000000 : ℝ), (4052870933/10000000000 : ℝ), (50660879/125000000 : ℝ)] ![(36043531877101/100000000000000 : ℝ), (15989118553397/50000000000000 : ℝ), (7994557750271/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(891176759/2000000000 : ℝ)|^4927 ≤ (36043531877101/100000000000000 : ℝ)^3903
        have hw : |(891176759/2000000000 : ℝ)|=(891176759/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4052870933/10000000000 : ℝ)|^4927 ≤ (15989118553397/50000000000000 : ℝ)^3903
        have hw : |(4052870933/10000000000 : ℝ)|=(4052870933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50660879/125000000 : ℝ)|^4927 ≤ (7994557750271/25000000000000 : ℝ)^3903
        have hw : |(50660879/125000000 : ℝ)|=(50660879/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_4 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1871882537/10000000000 : ℝ)*x 0 + (651974041/1250000000 : ℝ)*x 1 + (5215792963/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1871882537/10000000000 : ℝ)^4927 ≤ (603006433267/5000000000000 : ℝ)^3903 := by
    have hnat : (1871882537 : ℕ)^4927*5000000000000^3903 ≤ 603006433267^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1871882537 10000000000 603006433267 5000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (651974041/1250000000 : ℝ)^4927 ≤ (8793986456201/20000000000000 : ℝ)^3903 := by
    have hnat : (651974041 : ℕ)^4927*20000000000000^3903 ≤ 8793986456201^3903*1250000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651974041 1250000000 8793986456201 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215792963/10000000000 : ℝ)^4927 ≤ (43969939038617/100000000000000 : ℝ)^3903 := by
    have hnat : (5215792963 : ℕ)^4927*100000000000000^3903 ≤ 43969939038617^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215792963 10000000000 43969939038617 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1871882537/10000000000 : ℝ), (651974041/1250000000 : ℝ), (5215792963/10000000000 : ℝ)] ![(603006433267/5000000000000 : ℝ), (8793986456201/20000000000000 : ℝ), (43969939038617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1871882537/10000000000 : ℝ)|^4927 ≤ (603006433267/5000000000000 : ℝ)^3903
        have hw : |(-1871882537/10000000000 : ℝ)|=(1871882537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(651974041/1250000000 : ℝ)|^4927 ≤ (8793986456201/20000000000000 : ℝ)^3903
        have hw : |(651974041/1250000000 : ℝ)|=(651974041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215792963/10000000000 : ℝ)|^4927 ≤ (43969939038617/100000000000000 : ℝ)^3903
        have hw : |(5215792963/10000000000 : ℝ)|=(5215792963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_5 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1076530283/2000000000 : ℝ)*x 0 + (-41226449/250000000 : ℝ)*x 1 + (1303948077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1076530283/2000000000 : ℝ)^4927 ≤ (457530255423/1000000000000 : ℝ)^3903 := by
    have hnat : (1076530283 : ℕ)^4927*1000000000000^3903 ≤ 457530255423^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076530283 2000000000 457530255423 1000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41226449/250000000 : ℝ)^4927 ≤ (10277042376053/100000000000000 : ℝ)^3903 := by
    have hnat : (41226449 : ℕ)^4927*100000000000000^3903 ≤ 10277042376053^3903*250000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41226449 250000000 10277042376053 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303948077/2500000000 : ℝ)^4927 ≤ (43969932068167/100000000000000 : ℝ)^3903 := by
    have hnat : (1303948077 : ℕ)^4927*100000000000000^3903 ≤ 43969932068167^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303948077 2500000000 43969932068167 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1076530283/2000000000 : ℝ), (-41226449/250000000 : ℝ), (1303948077/2500000000 : ℝ)] ![(457530255423/1000000000000 : ℝ), (10277042376053/100000000000000 : ℝ), (43969932068167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1076530283/2000000000 : ℝ)|^4927 ≤ (457530255423/1000000000000 : ℝ)^3903
        have hw : |(1076530283/2000000000 : ℝ)|=(1076530283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41226449/250000000 : ℝ)|^4927 ≤ (10277042376053/100000000000000 : ℝ)^3903
        have hw : |(-41226449/250000000 : ℝ)|=(41226449/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1303948077/2500000000 : ℝ)|^4927 ≤ (43969932068167/100000000000000 : ℝ)^3903
        have hw : |(1303948077/2500000000 : ℝ)|=(1303948077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_6 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2691325437/5000000000 : ℝ)*x 0 + (5215792969/10000000000 : ℝ)*x 1 + (-412264451/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691325437/5000000000 : ℝ)^4927 ≤ (9150603947453/20000000000000 : ℝ)^3903 := by
    have hnat : (2691325437 : ℕ)^4927*20000000000000^3903 ≤ 9150603947453^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691325437 5000000000 9150603947453 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215792969/10000000000 : ℝ)^4927 ≤ (43969939102469/100000000000000 : ℝ)^3903 := by
    have hnat : (5215792969 : ℕ)^4927*100000000000000^3903 ≤ 43969939102469^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215792969 10000000000 43969939102469 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412264451/2500000000 : ℝ)^4927 ≤ (10277041148781/100000000000000 : ℝ)^3903 := by
    have hnat : (412264451 : ℕ)^4927*100000000000000^3903 ≤ 10277041148781^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412264451 2500000000 10277041148781 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691325437/5000000000 : ℝ), (5215792969/10000000000 : ℝ), (-412264451/2500000000 : ℝ)] ![(9150603947453/20000000000000 : ℝ), (43969939102469/100000000000000 : ℝ), (10277041148781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691325437/5000000000 : ℝ)|^4927 ≤ (9150603947453/20000000000000 : ℝ)^3903
        have hw : |(2691325437/5000000000 : ℝ)|=(2691325437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215792969/10000000000 : ℝ)|^4927 ≤ (43969939102469/100000000000000 : ℝ)^3903
        have hw : |(5215792969/10000000000 : ℝ)|=(5215792969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-412264451/2500000000 : ℝ)|^4927 ≤ (10277041148781/100000000000000 : ℝ)^3903
        have hw : |(-412264451/2500000000 : ℝ)|=(412264451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_7 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (779200889/2000000000 : ℝ)*x 0 + (541560761/1250000000 : ℝ)*x 1 + (1083121567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (779200889/2000000000 : ℝ)^4927 ≤ (76059494377/250000000000 : ℝ)^3903 := by
    have hnat : (779200889 : ℕ)^4927*250000000000^3903 ≤ 76059494377^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      779200889 2000000000 76059494377 250000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541560761/1250000000 : ℝ)^4927 ≤ (869702505067/2500000000000 : ℝ)^3903 := by
    have hnat : (541560761 : ℕ)^4927*2500000000000^3903 ≤ 869702505067^3903*1250000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541560761 1250000000 869702505067 2500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083121567/2500000000 : ℝ)^4927 ≤ (17394051013603/50000000000000 : ℝ)^3903 := by
    have hnat : (1083121567 : ℕ)^4927*50000000000000^3903 ≤ 17394051013603^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083121567 2500000000 17394051013603 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(779200889/2000000000 : ℝ), (541560761/1250000000 : ℝ), (1083121567/2500000000 : ℝ)] ![(76059494377/250000000000 : ℝ), (869702505067/2500000000000 : ℝ), (17394051013603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(779200889/2000000000 : ℝ)|^4927 ≤ (76059494377/250000000000 : ℝ)^3903
        have hw : |(779200889/2000000000 : ℝ)|=(779200889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541560761/1250000000 : ℝ)|^4927 ≤ (869702505067/2500000000000 : ℝ)^3903
        have hw : |(541560761/1250000000 : ℝ)|=(541560761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083121567/2500000000 : ℝ)|^4927 ≤ (17394051013603/50000000000000 : ℝ)^3903
        have hw : |(1083121567/2500000000 : ℝ)|=(1083121567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_8 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1759852941/10000000000 : ℝ)*x 0 + (5077818423/10000000000 : ℝ)*x 1 + (543700353/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1759852941/10000000000 : ℝ)^4927 ≤ (11156239691027/100000000000000 : ℝ)^3903 := by
    have hnat : (1759852941 : ℕ)^4927*100000000000000^3903 ≤ 11156239691027^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759852941 10000000000 11156239691027 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5077818423/10000000000 : ℝ)^4927 ≤ (531334442351/1250000000000 : ℝ)^3903 := by
    have hnat : (5077818423 : ℕ)^4927*1250000000000^3903 ≤ 531334442351^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077818423 10000000000 531334442351 1250000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543700353/1000000000 : ℝ)^4927 ≤ (46337004901079/100000000000000 : ℝ)^3903 := by
    have hnat : (543700353 : ℕ)^4927*100000000000000^3903 ≤ 46337004901079^3903*1000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543700353 1000000000 46337004901079 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1759852941/10000000000 : ℝ), (5077818423/10000000000 : ℝ), (543700353/1000000000 : ℝ)] ![(11156239691027/100000000000000 : ℝ), (531334442351/1250000000000 : ℝ), (46337004901079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1759852941/10000000000 : ℝ)|^4927 ≤ (11156239691027/100000000000000 : ℝ)^3903
        have hw : |(-1759852941/10000000000 : ℝ)|=(1759852941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5077818423/10000000000 : ℝ)|^4927 ≤ (531334442351/1250000000000 : ℝ)^3903
        have hw : |(5077818423/10000000000 : ℝ)|=(5077818423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543700353/1000000000 : ℝ)|^4927 ≤ (46337004901079/100000000000000 : ℝ)^3903
        have hw : |(543700353/1000000000 : ℝ)|=(543700353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_9 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230857727/10000000000 : ℝ)*x 0 + (-776853097/5000000000 : ℝ)*x 1 + (2718502079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230857727/10000000000 : ℝ)^4927 ≤ (1103257939553/2500000000000 : ℝ)^3903 := by
    have hnat : (5230857727 : ℕ)^4927*2500000000000^3903 ≤ 1103257939553^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230857727 10000000000 1103257939553 2500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (776853097/5000000000 : ℝ)^4927 ≤ (238316768609/2500000000000 : ℝ)^3903 := by
    have hnat : (776853097 : ℕ)^4927*2500000000000^3903 ≤ 238316768609^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776853097 5000000000 238316768609 2500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718502079/5000000000 : ℝ)^4927 ≤ (46337011657427/100000000000000 : ℝ)^3903 := by
    have hnat : (2718502079 : ℕ)^4927*100000000000000^3903 ≤ 46337011657427^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718502079 5000000000 46337011657427 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230857727/10000000000 : ℝ), (-776853097/5000000000 : ℝ), (2718502079/5000000000 : ℝ)] ![(1103257939553/2500000000000 : ℝ), (238316768609/2500000000000 : ℝ), (46337011657427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230857727/10000000000 : ℝ)|^4927 ≤ (1103257939553/2500000000000 : ℝ)^3903
        have hw : |(5230857727/10000000000 : ℝ)|=(5230857727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-776853097/5000000000 : ℝ)|^4927 ≤ (238316768609/2500000000000 : ℝ)^3903
        have hw : |(-776853097/5000000000 : ℝ)|=(776853097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718502079/5000000000 : ℝ)|^4927 ≤ (46337011657427/100000000000000 : ℝ)^3903
        have hw : |(2718502079/5000000000 : ℝ)|=(2718502079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_10 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230858023/10000000000 : ℝ)*x 0 + (2718502383/5000000000 : ℝ)*x 1 + (-776852471/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230858023/10000000000 : ℝ)^4927 ≤ (44130320734509/100000000000000 : ℝ)^3903 := by
    have hnat : (5230858023 : ℕ)^4927*100000000000000^3903 ≤ 44130320734509^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230858023 10000000000 44130320734509 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718502383/5000000000 : ℝ)^4927 ≤ (9267403639721/20000000000000 : ℝ)^3903 := by
    have hnat : (2718502383 : ℕ)^4927*20000000000000^3903 ≤ 9267403639721^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718502383 5000000000 9267403639721 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (776852471/5000000000 : ℝ)^4927 ≤ (2383165261859/25000000000000 : ℝ)^3903 := by
    have hnat : (776852471 : ℕ)^4927*25000000000000^3903 ≤ 2383165261859^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776852471 5000000000 2383165261859 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230858023/10000000000 : ℝ), (2718502383/5000000000 : ℝ), (-776852471/5000000000 : ℝ)] ![(44130320734509/100000000000000 : ℝ), (9267403639721/20000000000000 : ℝ), (2383165261859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230858023/10000000000 : ℝ)|^4927 ≤ (44130320734509/100000000000000 : ℝ)^3903
        have hw : |(5230858023/10000000000 : ℝ)|=(5230858023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718502383/5000000000 : ℝ)|^4927 ≤ (9267403639721/20000000000000 : ℝ)^3903
        have hw : |(2718502383/5000000000 : ℝ)|=(2718502383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-776852471/5000000000 : ℝ)|^4927 ≤ (2383165261859/25000000000000 : ℝ)^3903
        have hw : |(-776852471/5000000000 : ℝ)|=(776852471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_11 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4539427577/10000000000 : ℝ)*x 0 + (2004941719/5000000000 : ℝ)*x 1 + (801976089/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4539427577/10000000000 : ℝ)^4927 ≤ (3689870413189/10000000000000 : ℝ)^3903 := by
    have hnat : (4539427577 : ℕ)^4927*10000000000000^3903 ≤ 3689870413189^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539427577 10000000000 3689870413189 10000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2004941719/5000000000 : ℝ)^4927 ≤ (15775331394103/50000000000000 : ℝ)^3903 := by
    have hnat : (2004941719 : ℕ)^4927*50000000000000^3903 ≤ 15775331394103^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004941719 5000000000 15775331394103 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801976089/2000000000 : ℝ)^4927 ≤ (3943829132511/12500000000000 : ℝ)^3903 := by
    have hnat : (801976089 : ℕ)^4927*12500000000000^3903 ≤ 3943829132511^3903*2000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801976089 2000000000 3943829132511 12500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4539427577/10000000000 : ℝ), (2004941719/5000000000 : ℝ), (801976089/2000000000 : ℝ)] ![(3689870413189/10000000000000 : ℝ), (15775331394103/50000000000000 : ℝ), (3943829132511/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4539427577/10000000000 : ℝ)|^4927 ≤ (3689870413189/10000000000000 : ℝ)^3903
        have hw : |(4539427577/10000000000 : ℝ)|=(4539427577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2004941719/5000000000 : ℝ)|^4927 ≤ (15775331394103/50000000000000 : ℝ)^3903
        have hw : |(2004941719/5000000000 : ℝ)|=(2004941719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801976089/2000000000 : ℝ)|^4927 ≤ (3943829132511/12500000000000 : ℝ)^3903
        have hw : |(801976089/2000000000 : ℝ)|=(801976089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_12 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-728499061/5000000000 : ℝ)*x 0 + (554028937/1000000000 : ℝ)*x 1 + (1298994423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (728499061/5000000000 : ℝ)^4927 ≤ (21974661301/250000000000 : ℝ)^3903 := by
    have hnat : (728499061 : ℕ)^4927*250000000000^3903 ≤ 21974661301^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728499061 5000000000 21974661301 250000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (554028937/1000000000 : ℝ)^4927 ≤ (5931370442553/12500000000000 : ℝ)^3903 := by
    have hnat : (554028937 : ℕ)^4927*12500000000000^3903 ≤ 5931370442553^3903*1000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      554028937 1000000000 5931370442553 12500000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298994423/2500000000 : ℝ)^4927 ≤ (43759171923483/100000000000000 : ℝ)^3903 := by
    have hnat : (1298994423 : ℕ)^4927*100000000000000^3903 ≤ 43759171923483^3903*2500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298994423 2500000000 43759171923483 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-728499061/5000000000 : ℝ), (554028937/1000000000 : ℝ), (1298994423/2500000000 : ℝ)] ![(21974661301/250000000000 : ℝ), (5931370442553/12500000000000 : ℝ), (43759171923483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-728499061/5000000000 : ℝ)|^4927 ≤ (21974661301/250000000000 : ℝ)^3903
        have hw : |(-728499061/5000000000 : ℝ)|=(728499061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(554028937/1000000000 : ℝ)|^4927 ≤ (5931370442553/12500000000000 : ℝ)^3903
        have hw : |(554028937/1000000000 : ℝ)|=(554028937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298994423/2500000000 : ℝ)|^4927 ≤ (43759171923483/100000000000000 : ℝ)^3903
        have hw : |(1298994423/2500000000 : ℝ)|=(1298994423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_13 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396257679/10000000000 : ℝ)*x 0 + (-1657278387/10000000000 : ℝ)*x 1 + (259798887/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396257679/10000000000 : ℝ)^4927 ≤ (2294953588867/5000000000000 : ℝ)^3903 := by
    have hnat : (5396257679 : ℕ)^4927*5000000000000^3903 ≤ 2294953588867^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396257679 10000000000 2294953588867 5000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1657278387/10000000000 : ℝ)^4927 ≤ (2585438942317/25000000000000 : ℝ)^3903 := by
    have hnat : (1657278387 : ℕ)^4927*25000000000000^3903 ≤ 2585438942317^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1657278387 10000000000 2585438942317 25000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259798887/500000000 : ℝ)^4927 ≤ (8751834486757/20000000000000 : ℝ)^3903 := by
    have hnat : (259798887 : ℕ)^4927*20000000000000^3903 ≤ 8751834486757^3903*500000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259798887 500000000 8751834486757 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396257679/10000000000 : ℝ), (-1657278387/10000000000 : ℝ), (259798887/500000000 : ℝ)] ![(2294953588867/5000000000000 : ℝ), (2585438942317/25000000000000 : ℝ), (8751834486757/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396257679/10000000000 : ℝ)|^4927 ≤ (2294953588867/5000000000000 : ℝ)^3903
        have hw : |(5396257679/10000000000 : ℝ)|=(5396257679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1657278387/10000000000 : ℝ)|^4927 ≤ (2585438942317/25000000000000 : ℝ)^3903
        have hw : |(-1657278387/10000000000 : ℝ)|=(1657278387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(259798887/500000000 : ℝ)|^4927 ≤ (8751834486757/20000000000000 : ℝ)^3903
        have hw : |(259798887/500000000 : ℝ)|=(259798887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_14 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396257419/10000000000 : ℝ)*x 0 + (2597988821/5000000000 : ℝ)*x 1 + (-828639437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396257419/10000000000 : ℝ)^4927 ≤ (45899068985641/100000000000000 : ℝ)^3903 := by
    have hnat : (5396257419 : ℕ)^4927*100000000000000^3903 ≤ 45899068985641^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396257419 10000000000 45899068985641 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597988821/5000000000 : ℝ)^4927 ≤ (43759171391919/100000000000000 : ℝ)^3903 := by
    have hnat : (2597988821 : ℕ)^4927*100000000000000^3903 ≤ 43759171391919^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597988821 5000000000 43759171391919 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828639437/5000000000 : ℝ)^4927 ≤ (5170879802781/50000000000000 : ℝ)^3903 := by
    have hnat : (828639437 : ℕ)^4927*50000000000000^3903 ≤ 5170879802781^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828639437 5000000000 5170879802781 50000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396257419/10000000000 : ℝ), (2597988821/5000000000 : ℝ), (-828639437/5000000000 : ℝ)] ![(45899068985641/100000000000000 : ℝ), (43759171391919/100000000000000 : ℝ), (5170879802781/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396257419/10000000000 : ℝ)|^4927 ≤ (45899068985641/100000000000000 : ℝ)^3903
        have hw : |(5396257419/10000000000 : ℝ)|=(5396257419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597988821/5000000000 : ℝ)|^4927 ≤ (43759171391919/100000000000000 : ℝ)^3903
        have hw : |(2597988821/5000000000 : ℝ)|=(2597988821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-828639437/5000000000 : ℝ)|^4927 ≤ (5170879802781/50000000000000 : ℝ)^3903
        have hw : |(-828639437/5000000000 : ℝ)|=(828639437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1652_box_15 (p : ℝ) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (383652873/1000000000 : ℝ)*x 0 + (4361324743/10000000000 : ℝ)*x 1 + (2180661321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (383652873/1000000000 : ℝ)^4927 ≤ (5967735861809/20000000000000 : ℝ)^3903 := by
    have hnat : (383652873 : ℕ)^4927*20000000000000^3903 ≤ 5967735861809^3903*1000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383652873 1000000000 5967735861809 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4361324743/10000000000 : ℝ)^4927 ≤ (35080671007417/100000000000000 : ℝ)^3903 := by
    have hnat : (4361324743 : ℕ)^4927*100000000000000^3903 ≤ 35080671007417^3903*10000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4361324743 10000000000 35080671007417 100000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180661321/5000000000 : ℝ)^4927 ≤ (7016129934809/20000000000000 : ℝ)^3903 := by
    have hnat : (2180661321 : ℕ)^4927*20000000000000^3903 ≤ 7016129934809^3903*5000000000^4927 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180661321 5000000000 7016129934809 20000000000000 4927 3903 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4927/1024 : ℝ)) 4927 3903 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(383652873/1000000000 : ℝ), (4361324743/10000000000 : ℝ), (2180661321/5000000000 : ℝ)] ![(5967735861809/20000000000000 : ℝ), (35080671007417/100000000000000 : ℝ), (7016129934809/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(383652873/1000000000 : ℝ)|^4927 ≤ (5967735861809/20000000000000 : ℝ)^3903
        have hw : |(383652873/1000000000 : ℝ)|=(383652873/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4361324743/10000000000 : ℝ)|^4927 ≤ (35080671007417/100000000000000 : ℝ)^3903
        have hw : |(4361324743/10000000000 : ℝ)|=(4361324743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2180661321/5000000000 : ℝ)|^4927 ≤ (7016129934809/20000000000000 : ℝ)^3903
        have hw : |(2180661321/5000000000 : ℝ)|=(2180661321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1652_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179688539/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2033/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10681/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16269/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58647/100000 : ℝ) ∧ (81233/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (88243/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2033/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10681/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2033/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10681/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2033/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10681/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2033/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10681/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2033/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10681/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2033/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10681/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10681/100000 : ℝ) ^ (4923/1024 : ℝ) ≤ (427531327008891/20000000000000000000 : ℝ) := by
    have hpowers : (10681/100000 : ℝ)^4923 ≤ (427531327008891/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10681 : ℕ)^4923*20000000000000000000^1024 ≤ 427531327008891^1024*100000^4923 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10681 100000 427531327008891 20000000000000000000 4923 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10681/100000 : ℝ)) (X := (427531327008891/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2033/12500 : ℝ) ^ (4923/1024 : ℝ) ≤ (8069620856926199/50000000000000000000 : ℝ) := by
    have hpowers : (2033/12500 : ℝ)^4923 ≤ (8069620856926199/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2033 : ℕ)^4923*50000000000000000000^1024 ≤ 8069620856926199^1024*12500^4923 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2033 12500 8069620856926199 50000000000000000000 4923 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2033/12500 : ℝ)) (X := (8069620856926199/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000427531327008891/10000000000000000000 : ℝ) ≤ (10000088926399991/10000000000000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (10000427531327008891/10000000000000000000 : ℝ)^1024 ≤ (10000088926399991/10000000000000000 : ℝ)^4923 := by
      have hnat : (10000427531327008891 : ℕ)^1024*10000000000000000^4923 ≤ 10000088926399991^4923*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000427531327008891 10000000000000000000 10000088926399991 10000000000000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000088926399991/10000000000000000 : ℝ)) (X := (10000427531327008891/10000000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100018276898348896853/100000000000000000000 : ℝ) ≤ (10000380137913809/10000000000000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (100018276898348896853/100000000000000000000 : ℝ)^1024 ≤ (10000380137913809/10000000000000000 : ℝ)^4923 := by
      have hnat : (100018276898348896853 : ℕ)^1024*10000000000000000^4923 ≤ 10000380137913809^4923*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100018276898348896853 100000000000000000000 10000380137913809 10000000000000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000380137913809/10000000000000000 : ℝ)) (X := (100018276898348896853/100000000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25008069620856926199/25000000000000000000 : ℝ) ≤ (10000671349427627/10000000000000000 : ℝ) ^ (4923/1024 : ℝ) := by
    have hpowers : (25008069620856926199/25000000000000000000 : ℝ)^1024 ≤ (10000671349427627/10000000000000000 : ℝ)^4923 := by
      have hnat : (25008069620856926199 : ℕ)^1024*10000000000000000^4923 ≤ 10000671349427627^4923*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25008069620856926199 25000000000000000000 10000671349427627 10000000000000000 1024 4923 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000671349427627/10000000000000000 : ℝ)) (X := (25008069620856926199/25000000000000000000 : ℝ)) (by norm_num) 4923 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(427531327008891/20000000000000000000 : ℝ) ≤ ((18608091871910989879/18610000000000000000 : ℝ)+2*(48535252303/93050000000000 : ℝ)*(10681/100000 : ℝ))^(4923/1024 : ℝ) := by
    rw [show (18608091871910989879/18610000000000000000 : ℝ)+2*(48535252303/93050000000000 : ℝ)*(10681/100000 : ℝ)=(10000088926399991/10000000000000000 : ℝ) by norm_num, show 1+2*(427531327008891/20000000000000000000 : ℝ)=(10000427531327008891/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8069620856926199/50000000000000000000 : ℝ)+(427531327008891/20000000000000000000 : ℝ) ≤ ((18608091871910989879/18610000000000000000 : ℝ)+(48535252303/93050000000000 : ℝ)*((2033/12500 : ℝ)+(10681/100000 : ℝ)))^(4923/1024 : ℝ) := by
    rw [show (18608091871910989879/18610000000000000000 : ℝ)+(48535252303/93050000000000 : ℝ)*((2033/12500 : ℝ)+(10681/100000 : ℝ))=(10000380137913809/10000000000000000 : ℝ) by norm_num, show 1+(8069620856926199/50000000000000000000 : ℝ)+(427531327008891/20000000000000000000 : ℝ)=(100018276898348896853/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8069620856926199/50000000000000000000 : ℝ) ≤ ((18608091871910989879/18610000000000000000 : ℝ)+2*(48535252303/93050000000000 : ℝ)*(2033/12500 : ℝ))^(4923/1024 : ℝ) := by
    rw [show (18608091871910989879/18610000000000000000 : ℝ)+2*(48535252303/93050000000000 : ℝ)*(2033/12500 : ℝ)=(10000671349427627/10000000000000000 : ℝ) by norm_num, show 1+2*(8069620856926199/50000000000000000000 : ℝ)=(25008069620856926199/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18608091871910989879/18610000000000000000 : ℝ)*(X 1 0+X 2 0)+(48535252303/93050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10681/100000 : ℝ)) (hi := (2033/12500 : ℝ)) (c := (18608091871910989879/18610000000000000000 : ℝ)) (alpha := (48535252303/93050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18608091871910989879/18610000000000000000 : ℝ)*(X 0 1+X 2 1)+(48535252303/93050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10681/100000 : ℝ)) (hi := (2033/12500 : ℝ)) (c := (18608091871910989879/18610000000000000000 : ℝ)) (alpha := (48535252303/93050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18608091871910989879/18610000000000000000 : ℝ)*(X 0 2+X 1 2)+(48535252303/93050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4923/1024 : ℝ)) (lo := (10681/100000 : ℝ)) (hi := (2033/12500 : ℝ)) (c := (18608091871910989879/18610000000000000000 : ℝ)) (alpha := (48535252303/93050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-269351217/2000000000 : ℝ)*X 0 0+(5407573171/10000000000 : ℝ)*X 0 1+(270378663/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251052099/10000000000 : ℝ)*X 1 0+(-156676171/1000000000 : ℝ)*X 1 1+(2703786693/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2625525991/5000000000 : ℝ)*X 2 0+(5407573373/10000000000 : ℝ)*X 2 1+(-1566761889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((891176759/2000000000 : ℝ)*X 0 0+(4052870933/10000000000 : ℝ)*X 0 1+(50660879/125000000 : ℝ)*X 0 2+(891176759/2000000000 : ℝ)*X 1 0+(4052870933/10000000000 : ℝ)*X 1 1+(50660879/125000000 : ℝ)*X 1 2+(891176759/2000000000 : ℝ)*X 2 0+(4052870933/10000000000 : ℝ)*X 2 1+(50660879/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1871882537/10000000000 : ℝ)*X 0 0+(651974041/1250000000 : ℝ)*X 0 1+(5215792963/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1076530283/2000000000 : ℝ)*X 1 0+(-41226449/250000000 : ℝ)*X 1 1+(1303948077/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2691325437/5000000000 : ℝ)*X 2 0+(5215792969/10000000000 : ℝ)*X 2 1+(-412264451/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((779200889/2000000000 : ℝ)*X 0 0+(541560761/1250000000 : ℝ)*X 0 1+(1083121567/2500000000 : ℝ)*X 0 2+(779200889/2000000000 : ℝ)*X 1 0+(541560761/1250000000 : ℝ)*X 1 1+(1083121567/2500000000 : ℝ)*X 1 2+(779200889/2000000000 : ℝ)*X 2 0+(541560761/1250000000 : ℝ)*X 2 1+(1083121567/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1759852941/10000000000 : ℝ)*X 0 0+(5077818423/10000000000 : ℝ)*X 0 1+(543700353/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230857727/10000000000 : ℝ)*X 1 0+(-776853097/5000000000 : ℝ)*X 1 1+(2718502079/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230858023/10000000000 : ℝ)*X 2 0+(2718502383/5000000000 : ℝ)*X 2 1+(-776852471/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4539427577/10000000000 : ℝ)*X 0 0+(2004941719/5000000000 : ℝ)*X 0 1+(801976089/2000000000 : ℝ)*X 0 2+(4539427577/10000000000 : ℝ)*X 1 0+(2004941719/5000000000 : ℝ)*X 1 1+(801976089/2000000000 : ℝ)*X 1 2+(4539427577/10000000000 : ℝ)*X 2 0+(2004941719/5000000000 : ℝ)*X 2 1+(801976089/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-728499061/5000000000 : ℝ)*X 0 0+(554028937/1000000000 : ℝ)*X 0 1+(1298994423/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5396257679/10000000000 : ℝ)*X 1 0+(-1657278387/10000000000 : ℝ)*X 1 1+(259798887/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5396257419/10000000000 : ℝ)*X 2 0+(2597988821/5000000000 : ℝ)*X 2 1+(-828639437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((383652873/1000000000 : ℝ)*X 0 0+(4361324743/10000000000 : ℝ)*X 0 1+(2180661321/5000000000 : ℝ)*X 0 2+(383652873/1000000000 : ℝ)*X 1 0+(4361324743/10000000000 : ℝ)*X 1 1+(2180661321/5000000000 : ℝ)*X 1 2+(383652873/1000000000 : ℝ)*X 2 0+(4361324743/10000000000 : ℝ)*X 2 1+(2180661321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1652_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16269/25000 : ℝ) ≤ (-302754096566965822106183382668061/465250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4136409/20000000000000 : ℝ)*(lower0) + (4658949/20000000000000 : ℝ)*(lower3) + (126891/250000000000 : ℝ)*(lower4) + (881377143307047/50000000000000 : ℝ)*(major0) + (881377143307047/50000000000000 : ℝ)*(major1) + (881377143307047/50000000000000 : ℝ)*(major2) + (1413784543/20000000000000 : ℝ)*(sp1) + (602051/160000000000 : ℝ)*(sp2) + (574576417/50000000000000 : ℝ)*(sp3) + (2566189650930601/100000000000000 : ℝ)*(sp4) + (2566187236206227/100000000000000 : ℝ)*(sp5) + (1283096964423533/50000000000000 : ℝ)*(sp6) + (490502129832041/50000000000000 : ℝ)*(sp7) + (4654198341/100000000000000 : ℝ)*(sp12) + (245251352204229/25000000000000 : ℝ)*(f.failure) + (1283097152564471/50000000000000 : ℝ)*(f.sum) + (23101585062241/9305000000000000000000000000 : ℝ)*base66 + (7034220461043422687/930500000000000000000000000000000 : ℝ)*base68 + (1284431085670922687/930500000000000000000000000000000 : ℝ)*base70 + (3767262758800422687/930500000000000000000000000000000 : ℝ)*base72 + (5739851586431/2326250000000000000000000000 : ℝ)*base73 + (1411532892286422687/930500000000000000000000000000000 : ℝ)*base76 + (3803497447307577313/930500000000000000000000000000000 : ℝ)*base77 + (2418329825611077313/930500000000000000000000000000000 : ℝ)*base79 + (30774569350721/9305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11368569/2500000000000000000000 : ℝ)*base90 + (11368569/2500000000000000000000 : ℝ)*base92 + (11368569/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58647/100000 : ℝ) ≤ (545736191068099252027491048329961/930500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13731437/50000000000000 : ℝ)*(lower0) + (36658397/100000000000000 : ℝ)*(upper1) + (2702327/6250000000000 : ℝ)*(upper2) + (976027/2500000000000 : ℝ)*(upper3) + (1853437526561653/100000000000000 : ℝ)*(major0) + (1853437526561653/100000000000000 : ℝ)*(major1) + (1853437526561653/100000000000000 : ℝ)*(major2) + (265585244282413/10000000000000 : ℝ)*(sp0) + (663962695917423/25000000000000 : ℝ)*(sp1) + (132792585398411/5000000000000 : ℝ)*(sp2) + (515736155704859/50000000000000 : ℝ)*(sp3) + (507950269/25000000000000 : ℝ)*(sp5) + (276875637/25000000000000 : ℝ)*(sp6) + (372646639/100000000000000 : ℝ)*(sp12) + (515736155704859/50000000000000 : ℝ)*(f.failure) + (165990800966923/6250000000000 : ℝ)*(f.sum) + (34147980332777/2326250000000000000000000000 : ℝ)*base65 + (12777444531069690013/1861000000000000000000000000000000 : ℝ)*base68 + (8271666132103690013/1861000000000000000000000000000000 : ℝ)*base70 + (7073739548186309987/1861000000000000000000000000000000 : ℝ)*base71 + (70450655611/290781250000000000000000000 : ℝ)*base74 + (729776661155690013/1861000000000000000000000000000000 : ℝ)*base76 + (24459477960597690013/1861000000000000000000000000000000 : ℝ)*base78 + (2607726435198309987/1861000000000000000000000000000000 : ℝ)*base79 + (14548970341311/4652500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (21088999/5000000000000000000000 : ℝ)*base90 + (21088999/5000000000000000000000 : ℝ)*base92 + (21088999/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (81233/100000 : ℝ) ≤ (188973707510177725218237971956149/232625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63959273/50000000000000 : ℝ)*(upper3) + (112710109/25000000000000 : ℝ)*(upper4) + (43054401/50000000000000 : ℝ)*(lower5) + (973748011155623/50000000000000 : ℝ)*(major0) + (973748011155623/50000000000000 : ℝ)*(major1) + (973748011155623/50000000000000 : ℝ)*(major2) + (11916059651/100000000000000 : ℝ)*(sp0) + (27859264903/100000000000000 : ℝ)*(sp1) + (210306077367/100000000000000 : ℝ)*(sp2) + (59944304973/100000000000000 : ℝ)*(sp3) + (348010509479531/12500000000000 : ℝ)*(sp8) + (696017033157749/25000000000000 : ℝ)*(sp9) + (695971421454633/25000000000000 : ℝ)*(sp10) + (21675153241303/2000000000000 : ℝ)*(sp11) + (270954401592531/25000000000000 : ℝ)*(f.failure) + (2784095991895899/100000000000000 : ℝ)*(f.sum) + (2408931832717/4652500000000000000000000000 : ℝ)*base66 + (4242598654113739617/930500000000000000000000000000000 : ℝ)*base67 + (3794167370895739617/930500000000000000000000000000000 : ℝ)*base69 + (934405179993739617/930500000000000000000000000000000 : ℝ)*base71 + (79603053646801/9305000000000000000000000000 : ℝ)*base73 + (1628088778102739617/930500000000000000000000000000000 : ℝ)*base75 + (2513011325793239617/930500000000000000000000000000000 : ℝ)*base77 + (366588597515260383/930500000000000000000000000000000 : ℝ)*base80 + (22244618552661/9305000000000000000000000000 : ℝ)*base81 + (18702209/2500000000000000000000 : ℝ)*base89 + (18702209/2500000000000000000000 : ℝ)*base91 + (18702209/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-88243/100000 : ℝ) ≤ (-410538190348858202200107845508663/465250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (106521929/100000000000000 : ℝ)*(upper1) + (143545481/50000000000000 : ℝ)*(upper3) + (10888887/25000000000000 : ℝ)*(lower4) + (1991670928865899/100000000000000 : ℝ)*(major0) + (1991670928865899/100000000000000 : ℝ)*(major1) + (1991670928865899/100000000000000 : ℝ)*(major2) + (5189706797/100000000000000 : ℝ)*(sp4) + (89283644103/100000000000000 : ℝ)*(sp5) + (65794835691/100000000000000 : ℝ)*(sp6) + (3905893169/10000000000000 : ℝ)*(sp7) + (1452174177630357/50000000000000 : ℝ)*(sp12) + (181516516332713/6250000000000 : ℝ)*(sp13) + (2904287750131821/100000000000000 : ℝ)*(sp14) + (1108362701108163/100000000000000 : ℝ)*(sp15) + (554200880019927/50000000000000 : ℝ)*(f.failure) + (363044193120939/12500000000000 : ℝ)*(f.sum) + (5227959748821/9305000000000000000000000000 : ℝ)*base66 + (9053610275091636221/1861000000000000000000000000000000 : ℝ)*base67 + (53914779986951636221/1861000000000000000000000000000000 : ℝ)*base69 + (9894742464579636221/1861000000000000000000000000000000 : ℝ)*base71 + (21587085872629/9305000000000000000000000000 : ℝ)*base73 + (3649739092793363779/1861000000000000000000000000000000 : ℝ)*base76 + (3092846726263636221/1861000000000000000000000000000000 : ℝ)*base77 + (898821675126636221/1861000000000000000000000000000000 : ℝ)*base79 + (16681214713577/4652500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (23516653/5000000000000000000000 : ℝ)*base89 + (23516653/5000000000000000000000 : ℝ)*base91 + (23516653/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1652_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179688539/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2033/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10681/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16269/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58647/100000 : ℝ) else (81233/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88243/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1652_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1652_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179688539/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16269/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58647/100000 : ℝ) else (81233/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88243/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1652_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1652_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1652_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4923/1024 : ℝ) ≤ p) (hpb : p ≤ (4927/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (179688539/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16339/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10613/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16269/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58647/100000 : ℝ) else (81233/100000 : ℝ) ≤ X j i ∧ X j i ≤ (88243/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1652_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
