-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1411_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:48:47.74656+00:00
-- url     : https://prove2.me/submissions/b9a5ba0a-eb5a-42f3-8188-9bd74ea5402a

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
theorem support_rectangle_w1411_s3_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984655299/10000000000 : ℝ)*x 0 + (5419140697/10000000000 : ℝ)*x 1 + (5237269/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984655299/10000000000 : ℝ)^4371 ≤ (3025205793893/25000000000000 : ℝ)^3347 := by
    have hnat : (1984655299 : ℕ)^4371*25000000000000^3347 ≤ 3025205793893^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984655299 10000000000 3025205793893 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419140697/10000000000 : ℝ)^4371 ≤ (44929088238511/100000000000000 : ℝ)^3347 := by
    have hnat : (5419140697 : ℕ)^4371*100000000000000^3347 ≤ 44929088238511^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419140697 10000000000 44929088238511 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237269/10000000 : ℝ)^4371 ≤ (21485044283371/50000000000000 : ℝ)^3347 := by
    have hnat : (5237269 : ℕ)^4371*50000000000000^3347 ≤ 21485044283371^3347*10000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237269 10000000 21485044283371 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984655299/10000000000 : ℝ), (5419140697/10000000000 : ℝ), (5237269/10000000 : ℝ)] ![(3025205793893/25000000000000 : ℝ), (44929088238511/100000000000000 : ℝ), (21485044283371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984655299/10000000000 : ℝ)|^4371 ≤ (3025205793893/25000000000000 : ℝ)^3347
        have hw : |(-1984655299/10000000000 : ℝ)|=(1984655299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419140697/10000000000 : ℝ)|^4371 ≤ (44929088238511/100000000000000 : ℝ)^3347
        have hw : |(5419140697/10000000000 : ℝ)|=(5419140697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237269/10000000 : ℝ)|^4371 ≤ (21485044283371/50000000000000 : ℝ)^3347
        have hw : |(5237269/10000000 : ℝ)|=(5237269/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s3_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337568329/2500000000 : ℝ)*x 0 + (-519365057/2500000000 : ℝ)*x 1 + (5237268917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337568329/2500000000 : ℝ)^4371 ≤ (22092445334641/50000000000000 : ℝ)^3347 := by
    have hnat : (1337568329 : ℕ)^4371*50000000000000^3347 ≤ 22092445334641^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337568329 2500000000 22092445334641 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519365057/2500000000 : ℝ)^4371 ≤ (12845021646927/100000000000000 : ℝ)^3347 := by
    have hnat : (519365057 : ℕ)^4371*100000000000000^3347 ≤ 12845021646927^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519365057 2500000000 12845021646927 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5237268917/10000000000 : ℝ)^4371 ≤ (42970087677409/100000000000000 : ℝ)^3347 := by
    have hnat : (5237268917 : ℕ)^4371*100000000000000^3347 ≤ 42970087677409^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237268917 10000000000 42970087677409 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337568329/2500000000 : ℝ), (-519365057/2500000000 : ℝ), (5237268917/10000000000 : ℝ)] ![(22092445334641/50000000000000 : ℝ), (12845021646927/100000000000000 : ℝ), (42970087677409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337568329/2500000000 : ℝ)|^4371 ≤ (22092445334641/50000000000000 : ℝ)^3347
        have hw : |(1337568329/2500000000 : ℝ)|=(1337568329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-519365057/2500000000 : ℝ)|^4371 ≤ (12845021646927/100000000000000 : ℝ)^3347
        have hw : |(-519365057/2500000000 : ℝ)|=(519365057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5237268917/10000000000 : ℝ)|^4371 ≤ (42970087677409/100000000000000 : ℝ)^3347
        have hw : |(5237268917/10000000000 : ℝ)|=(5237268917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s3_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675136633/5000000000 : ℝ)*x 0 + (2618634513/5000000000 : ℝ)*x 1 + (-41549203/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675136633/5000000000 : ℝ)^4371 ≤ (11046222532507/25000000000000 : ℝ)^3347 := by
    have hnat : (2675136633 : ℕ)^4371*25000000000000^3347 ≤ 11046222532507^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675136633 5000000000 11046222532507 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2618634513/5000000000 : ℝ)^4371 ≤ (42970088845329/100000000000000 : ℝ)^3347 := by
    have hnat : (2618634513 : ℕ)^4371*100000000000000^3347 ≤ 42970088845329^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2618634513 5000000000 42970088845329 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41549203/200000000 : ℝ)^4371 ≤ (128450210171/1000000000000 : ℝ)^3347 := by
    have hnat : (41549203 : ℕ)^4371*1000000000000^3347 ≤ 128450210171^3347*200000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41549203 200000000 128450210171 1000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675136633/5000000000 : ℝ), (2618634513/5000000000 : ℝ), (-41549203/200000000 : ℝ)] ![(11046222532507/25000000000000 : ℝ), (42970088845329/100000000000000 : ℝ), (128450210171/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675136633/5000000000 : ℝ)|^4371 ≤ (11046222532507/25000000000000 : ℝ)^3347
        have hw : |(2675136633/5000000000 : ℝ)|=(2675136633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2618634513/5000000000 : ℝ)|^4371 ≤ (42970088845329/100000000000000 : ℝ)^3347
        have hw : |(2618634513/5000000000 : ℝ)|=(2618634513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41549203/200000000 : ℝ)|^4371 ≤ (128450210171/1000000000000 : ℝ)^3347
        have hw : |(-41549203/200000000 : ℝ)|=(41549203/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s3_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (430817859/1000000000 : ℝ)*x 0 + (823353461/2000000000 : ℝ)*x 1 + (4507623279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430817859/1000000000 : ℝ)^4371 ≤ (8324295036721/25000000000000 : ℝ)^3347 := by
    have hnat : (430817859 : ℕ)^4371*25000000000000^3347 ≤ 8324295036721^3347*1000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430817859 1000000000 8324295036721 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (823353461/2000000000 : ℝ)^4371 ≤ (31378451873739/100000000000000 : ℝ)^3347 := by
    have hnat : (823353461 : ℕ)^4371*100000000000000^3347 ≤ 31378451873739^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      823353461 2000000000 31378451873739 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4507623279/10000000000 : ℝ)^4371 ≤ (35324367959783/100000000000000 : ℝ)^3347 := by
    have hnat : (4507623279 : ℕ)^4371*100000000000000^3347 ≤ 35324367959783^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4507623279 10000000000 35324367959783 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(430817859/1000000000 : ℝ), (823353461/2000000000 : ℝ), (4507623279/10000000000 : ℝ)] ![(8324295036721/25000000000000 : ℝ), (31378451873739/100000000000000 : ℝ), (35324367959783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(430817859/1000000000 : ℝ)|^4371 ≤ (8324295036721/25000000000000 : ℝ)^3347
        have hw : |(430817859/1000000000 : ℝ)|=(430817859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(823353461/2000000000 : ℝ)|^4371 ≤ (31378451873739/100000000000000 : ℝ)^3347
        have hw : |(823353461/2000000000 : ℝ)|=(823353461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4507623279/10000000000 : ℝ)|^4371 ≤ (35324367959783/100000000000000 : ℝ)^3347
        have hw : |(4507623279/10000000000 : ℝ)|=(4507623279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s3_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1984671639/10000000000 : ℝ)*x 0 + (654750089/1250000000 : ℝ)*x 1 + (270920227/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1984671639/10000000000 : ℝ)^4371 ≤ (6050476642313/50000000000000 : ℝ)^3347 := by
    have hnat : (1984671639 : ℕ)^4371*50000000000000^3347 ≤ 6050476642313^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1984671639 10000000000 6050476642313 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654750089/1250000000 : ℝ)^4371 ≤ (10744482231309/25000000000000 : ℝ)^3347 := by
    have hnat : (654750089 : ℕ)^4371*25000000000000^3347 ≤ 10744482231309^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654750089 1250000000 10744482231309 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270920227/500000000 : ℝ)^4371 ≤ (359368942183/800000000000 : ℝ)^3347 := by
    have hnat : (270920227 : ℕ)^4371*800000000000^3347 ≤ 359368942183^3347*500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270920227 500000000 359368942183 800000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1984671639/10000000000 : ℝ), (654750089/1250000000 : ℝ), (270920227/500000000 : ℝ)] ![(6050476642313/50000000000000 : ℝ), (10744482231309/25000000000000 : ℝ), (359368942183/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1984671639/10000000000 : ℝ)|^4371 ≤ (6050476642313/50000000000000 : ℝ)^3347
        have hw : |(-1984671639/10000000000 : ℝ)|=(1984671639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654750089/1250000000 : ℝ)|^4371 ≤ (10744482231309/25000000000000 : ℝ)^3347
        have hw : |(654750089/1250000000 : ℝ)|=(654750089/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270920227/500000000 : ℝ)|^4371 ≤ (359368942183/800000000000 : ℝ)^3347
        have hw : |(270920227/500000000 : ℝ)|=(270920227/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s3_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651538499/5000000000 : ℝ)*x 0 + (-379264821/2000000000 : ℝ)*x 1 + (541840479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651538499/5000000000 : ℝ)^4371 ≤ (2729785214069/6250000000000 : ℝ)^3347 := by
    have hnat : (2651538499 : ℕ)^4371*6250000000000^3347 ≤ 2729785214069^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651538499 5000000000 2729785214069 6250000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379264821/2000000000 : ℝ)^4371 ≤ (2850579019153/25000000000000 : ℝ)^3347 := by
    have hnat : (379264821 : ℕ)^4371*25000000000000^3347 ≤ 2850579019153^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379264821 2000000000 2850579019153 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541840479/1000000000 : ℝ)^4371 ≤ (44921120479601/100000000000000 : ℝ)^3347 := by
    have hnat : (541840479 : ℕ)^4371*100000000000000^3347 ≤ 44921120479601^3347*1000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541840479 1000000000 44921120479601 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651538499/5000000000 : ℝ), (-379264821/2000000000 : ℝ), (541840479/1000000000 : ℝ)] ![(2729785214069/6250000000000 : ℝ), (2850579019153/25000000000000 : ℝ), (44921120479601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651538499/5000000000 : ℝ)|^4371 ≤ (2729785214069/6250000000000 : ℝ)^3347
        have hw : |(2651538499/5000000000 : ℝ)|=(2651538499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-379264821/2000000000 : ℝ)|^4371 ≤ (2850579019153/25000000000000 : ℝ)^3347
        have hw : |(-379264821/2000000000 : ℝ)|=(379264821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541840479/1000000000 : ℝ)|^4371 ≤ (44921120479601/100000000000000 : ℝ)^3347
        have hw : |(541840479/1000000000 : ℝ)|=(541840479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s3_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265153887/500000000 : ℝ)*x 0 + (5418404179/10000000000 : ℝ)*x 1 + (-1896323931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265153887/500000000 : ℝ)^4371 ≤ (43676571405961/100000000000000 : ℝ)^3347 := by
    have hnat : (265153887 : ℕ)^4371*100000000000000^3347 ≤ 43676571405961^3347*500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265153887 500000000 43676571405961 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5418404179/10000000000 : ℝ)^4371 ≤ (11230278466091/25000000000000 : ℝ)^3347 := by
    have hnat : (5418404179 : ℕ)^4371*25000000000000^3347 ≤ 11230278466091^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5418404179 10000000000 11230278466091 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1896323931/10000000000 : ℝ)^4371 ≤ (2280462942057/20000000000000 : ℝ)^3347 := by
    have hnat : (1896323931 : ℕ)^4371*20000000000000^3347 ≤ 2280462942057^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896323931 10000000000 2280462942057 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265153887/500000000 : ℝ), (5418404179/10000000000 : ℝ), (-1896323931/10000000000 : ℝ)] ![(43676571405961/100000000000000 : ℝ), (11230278466091/25000000000000 : ℝ), (2280462942057/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265153887/500000000 : ℝ)|^4371 ≤ (43676571405961/100000000000000 : ℝ)^3347
        have hw : |(265153887/500000000 : ℝ)|=(265153887/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5418404179/10000000000 : ℝ)|^4371 ≤ (11230278466091/25000000000000 : ℝ)^3347
        have hw : |(5418404179/10000000000 : ℝ)|=(5418404179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1896323931/10000000000 : ℝ)|^4371 ≤ (2280462942057/20000000000000 : ℝ)^3347
        have hw : |(-1896323931/10000000000 : ℝ)|=(1896323931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s3_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (861642787/2000000000 : ℝ)*x 0 + (56325631/125000000 : ℝ)*x 1 + (4118348341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861642787/2000000000 : ℝ)^4371 ≤ (16648768449839/50000000000000 : ℝ)^3347 := by
    have hnat : (861642787 : ℕ)^4371*50000000000000^3347 ≤ 16648768449839^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861642787 2000000000 16648768449839 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56325631/125000000 : ℝ)^4371 ≤ (8827068138573/25000000000000 : ℝ)^3347 := by
    have hnat : (56325631 : ℕ)^4371*25000000000000^3347 ≤ 8827068138573^3347*125000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56325631 125000000 8827068138573 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4118348341/10000000000 : ℝ)^4371 ≤ (6278838105327/20000000000000 : ℝ)^3347 := by
    have hnat : (4118348341 : ℕ)^4371*20000000000000^3347 ≤ 6278838105327^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118348341 10000000000 6278838105327 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(861642787/2000000000 : ℝ), (56325631/125000000 : ℝ), (4118348341/10000000000 : ℝ)] ![(16648768449839/50000000000000 : ℝ), (8827068138573/25000000000000 : ℝ), (6278838105327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(861642787/2000000000 : ℝ)|^4371 ≤ (16648768449839/50000000000000 : ℝ)^3347
        have hw : |(861642787/2000000000 : ℝ)|=(861642787/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56325631/125000000 : ℝ)|^4371 ≤ (8827068138573/25000000000000 : ℝ)^3347
        have hw : |(56325631/125000000 : ℝ)|=(56325631/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4118348341/10000000000 : ℝ)|^4371 ≤ (6278838105327/20000000000000 : ℝ)^3347
        have hw : |(4118348341/10000000000 : ℝ)|=(4118348341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (991/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5553/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14957/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (991/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (991/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (991/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (991/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (991/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (991/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10269/100000 : ℝ) ^ (2185/512 : ℝ) ≤ (6048102910524323/100000000000000000000 : ℝ) := by
    have hpowers : (10269/100000 : ℝ)^2185 ≤ (6048102910524323/100000000000000000000 : ℝ)^512 := by
      have hnat : (10269 : ℕ)^2185*100000000000000000000^512 ≤ 6048102910524323^512*100000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10269 100000 6048102910524323 100000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10269/100000 : ℝ)) (X := (6048102910524323/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (991/6250 : ℝ) ^ (2185/512 : ℝ) ≤ (9653923883607823/25000000000000000000 : ℝ) := by
    have hpowers : (991/6250 : ℝ)^2185 ≤ (9653923883607823/25000000000000000000 : ℝ)^512 := by
      have hnat : (991 : ℕ)^2185*25000000000000000000^512 ≤ 9653923883607823^512*6250^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        991 6250 9653923883607823 25000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (991/6250 : ℝ)) (X := (9653923883607823/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006048102910524323/50000000000000000000 : ℝ) ≤ (2500070857787167/2500000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (50006048102910524323/50000000000000000000 : ℝ)^512 ≤ (2500070857787167/2500000000000000 : ℝ)^2185 := by
      have hnat : (50006048102910524323 : ℕ)^512*2500000000000000^2185 ≤ 2500070857787167^2185*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006048102910524323 50000000000000000000 2500070857787167 2500000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500070857787167/2500000000000000 : ℝ)) (X := (50006048102910524323/50000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008932759688991123/20000000000000000000 : ℝ) ≤ (10001046405293371/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (20008932759688991123/20000000000000000000 : ℝ)^512 ≤ (10001046405293371/10000000000000000 : ℝ)^2185 := by
      have hnat : (20008932759688991123 : ℕ)^512*10000000000000000^2185 ≤ 10001046405293371^2185*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008932759688991123 20000000000000000000 10001046405293371 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001046405293371/10000000000000000 : ℝ)) (X := (20008932759688991123/20000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509653923883607823/12500000000000000000 : ℝ) ≤ (5000904689719037/5000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (12509653923883607823/12500000000000000000 : ℝ)^512 ≤ (5000904689719037/5000000000000000 : ℝ)^2185 := by
      have hnat : (12509653923883607823 : ℕ)^512*5000000000000000^2185 ≤ 5000904689719037^2185*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509653923883607823 12500000000000000000 5000904689719037 5000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000904689719037/5000000000000000 : ℝ)) (X := (12509653923883607823/12500000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6048102910524323/100000000000000000000 : ℝ) ≤ ((27927956783421848951/27935000000000000000 : ℝ)+2*(762974144703/558700000000000 : ℝ)*(10269/100000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (27927956783421848951/27935000000000000000 : ℝ)+2*(762974144703/558700000000000 : ℝ)*(10269/100000 : ℝ)=(2500070857787167/2500000000000000 : ℝ) by norm_num, show 1+2*(6048102910524323/100000000000000000000 : ℝ)=(50006048102910524323/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9653923883607823/25000000000000000000 : ℝ)+(6048102910524323/100000000000000000000 : ℝ) ≤ ((27927956783421848951/27935000000000000000 : ℝ)+(762974144703/558700000000000 : ℝ)*((991/6250 : ℝ)+(10269/100000 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (27927956783421848951/27935000000000000000 : ℝ)+(762974144703/558700000000000 : ℝ)*((991/6250 : ℝ)+(10269/100000 : ℝ))=(10001046405293371/10000000000000000 : ℝ) by norm_num, show 1+(9653923883607823/25000000000000000000 : ℝ)+(6048102910524323/100000000000000000000 : ℝ)=(20008932759688991123/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9653923883607823/25000000000000000000 : ℝ) ≤ ((27927956783421848951/27935000000000000000 : ℝ)+2*(762974144703/558700000000000 : ℝ)*(991/6250 : ℝ))^(2185/512 : ℝ) := by
    rw [show (27927956783421848951/27935000000000000000 : ℝ)+2*(762974144703/558700000000000 : ℝ)*(991/6250 : ℝ)=(5000904689719037/5000000000000000 : ℝ) by norm_num, show 1+2*(9653923883607823/25000000000000000000 : ℝ)=(12509653923883607823/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27927956783421848951/27935000000000000000 : ℝ)*(X 1 0+X 2 0)+(762974144703/558700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (10269/100000 : ℝ)) (hi := (991/6250 : ℝ)) (c := (27927956783421848951/27935000000000000000 : ℝ)) (alpha := (762974144703/558700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27927956783421848951/27935000000000000000 : ℝ)*(X 0 1+X 2 1)+(762974144703/558700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (10269/100000 : ℝ)) (hi := (991/6250 : ℝ)) (c := (27927956783421848951/27935000000000000000 : ℝ)) (alpha := (762974144703/558700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27927956783421848951/27935000000000000000 : ℝ)*(X 0 2+X 1 2)+(762974144703/558700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (10269/100000 : ℝ)) (hi := (991/6250 : ℝ)) (c := (27927956783421848951/27935000000000000000 : ℝ)) (alpha := (762974144703/558700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1984655299/10000000000 : ℝ)*X 0 0+(5419140697/10000000000 : ℝ)*X 0 1+(5237269/10000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337568329/2500000000 : ℝ)*X 1 0+(-519365057/2500000000 : ℝ)*X 1 1+(5237268917/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675136633/5000000000 : ℝ)*X 2 0+(2618634513/5000000000 : ℝ)*X 2 1+(-41549203/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((430817859/1000000000 : ℝ)*X 0 0+(823353461/2000000000 : ℝ)*X 0 1+(4507623279/10000000000 : ℝ)*X 0 2+(430817859/1000000000 : ℝ)*X 1 0+(823353461/2000000000 : ℝ)*X 1 1+(4507623279/10000000000 : ℝ)*X 1 2+(430817859/1000000000 : ℝ)*X 2 0+(823353461/2000000000 : ℝ)*X 2 1+(4507623279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1984671639/10000000000 : ℝ)*X 0 0+(654750089/1250000000 : ℝ)*X 0 1+(270920227/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2651538499/5000000000 : ℝ)*X 1 0+(-379264821/2000000000 : ℝ)*X 1 1+(541840479/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265153887/500000000 : ℝ)*X 2 0+(5418404179/10000000000 : ℝ)*X 2 1+(-1896323931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((861642787/2000000000 : ℝ)*X 0 0+(56325631/125000000 : ℝ)*X 0 1+(4118348341/10000000000 : ℝ)*X 0 2+(861642787/2000000000 : ℝ)*X 1 0+(56325631/125000000 : ℝ)*X 1 1+(4118348341/10000000000 : ℝ)*X 1 2+(861642787/2000000000 : ℝ)*X 2 0+(56325631/125000000 : ℝ)*X 2 1+(4118348341/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2578445357293498483276104069/698375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (385372059/50000000000000 : ℝ)*(base19) + (131907023/20000000000000 : ℝ)*(base23) + (43237383/50000000000000 : ℝ)*(upper3) + (32007831/100000000000000 : ℝ)*(upper4) + (124298323/100000000000000 : ℝ)*(upper5) + (4028452020183551/100000000000000 : ℝ)*(major0) + (4028452020183551/100000000000000 : ℝ)*(major1) + (7868070351921/195312500000 : ℝ)*(major2) + (5498392812993401/100000000000000 : ℝ)*(sp0) + (2749202507238927/50000000000000 : ℝ)*(sp1) + (5498405125686857/100000000000000 : ℝ)*(sp2) + (2558492867218679/100000000000000 : ℝ)*(sp3) + (12972228571/100000000000000 : ℝ)*(sp4) + (1316214409/25000000000000 : ℝ)*(sp7) + (639624533019079/25000000000000 : ℝ)*(f.failure) + (1374601446305493/25000000000000 : ℝ)*(f.sum) + (193372601658669/55870000000000000000000000000 : ℝ)*base65 + (6932406683625605001/2793500000000000000000000000000000 : ℝ)*base67 + (1820085662714175247/174593750000000000000000000000000 : ℝ)*base69 + (3796016542740605001/2793500000000000000000000000000000 : ℝ)*base71 + (134238136816401/55870000000000000000000000000 : ℝ)*base74 + (1740980241442737747/174593750000000000000000000000000 : ℝ)*base75 + (17821684648242455001/2793500000000000000000000000000000 : ℝ)*base77 + (28501678127504955001/2793500000000000000000000000000000 : ℝ)*base79 + (21175635802401/3491875000000000000000000000 : ℝ)*base81 + (1283431/125000000000000000000 : ℝ)*base89 + (1283431/125000000000000000000 : ℝ)*base91 + (33431/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8546557892461637495363816877/1396750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570338049/20000000000000 : ℝ)*(base19) + (191723337/5000000000000 : ℝ)*(base23) + (213783291/50000000000000 : ℝ)*(upper3) + (10670991/25000000000000 : ℝ)*(lower4) + (278099237/100000000000000 : ℝ)*(upper5) + (4061211913531591/100000000000000 : ℝ)*(major0) + (4061211913531591/100000000000000 : ℝ)*(major1) + (4061211913531591/100000000000000 : ℝ)*(major2) + (56175534013/100000000000000 : ℝ)*(sp1) + (70413165371/100000000000000 : ℝ)*(sp2) + (5543119452992899/100000000000000 : ℝ)*(sp4) + (5543060425768641/100000000000000 : ℝ)*(sp5) + (5543045205360789/100000000000000 : ℝ)*(sp6) + (257930417010731/10000000000000 : ℝ)*(sp7) + (257930417010731/10000000000000 : ℝ)*(f.failure) + (5543119452992899/100000000000000 : ℝ)*(f.sum) + (9486164845379/13967500000000000000000000000 : ℝ)*base65 + (28801585355364361041/2793500000000000000000000000000000 : ℝ)*base67 + (40105535394097361041/2793500000000000000000000000000000 : ℝ)*base69 + (48921129986086361041/2793500000000000000000000000000000 : ℝ)*base71 + (25322733077247/6983750000000000000000000000 : ℝ)*base73 + (3076395570171138959/2793500000000000000000000000000000 : ℝ)*base76 + (5138379533733638959/2793500000000000000000000000000000 : ℝ)*base78 + (9298788042792861041/2793500000000000000000000000000000 : ℝ)*base79 + (127168049521019/13967500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (674341/50000000000000000000 : ℝ)*base90 + (674341/50000000000000000000 : ℝ)*base92 + (674341/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1411_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (991/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5553/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14957/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1411_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1411_s4_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1985648621/10000000000 : ℝ)*x 0 + (5410713903/10000000000 : ℝ)*x 1 + (1049008449/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985648621/10000000000 : ℝ)^4371 ≤ (6054366603609/50000000000000 : ℝ)^3347 := by
    have hnat : (1985648621 : ℕ)^4371*50000000000000^3347 ≤ 6054366603609^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985648621 10000000000 6054366603609 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410713903/10000000000 : ℝ)^4371 ≤ (44837870081487/100000000000000 : ℝ)^3347 := by
    have hnat : (5410713903 : ℕ)^4371*100000000000000^3347 ≤ 44837870081487^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410713903 10000000000 44837870081487 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049008449/2000000000 : ℝ)^4371 ≤ (10763349173773/25000000000000 : ℝ)^3347 := by
    have hnat : (1049008449 : ℕ)^4371*25000000000000^3347 ≤ 10763349173773^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049008449 2000000000 10763349173773 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1985648621/10000000000 : ℝ), (5410713903/10000000000 : ℝ), (1049008449/2000000000 : ℝ)] ![(6054366603609/50000000000000 : ℝ), (44837870081487/100000000000000 : ℝ), (10763349173773/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1985648621/10000000000 : ℝ)|^4371 ≤ (6054366603609/50000000000000 : ℝ)^3347
        have hw : |(-1985648621/10000000000 : ℝ)|=(1985648621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410713903/10000000000 : ℝ)|^4371 ≤ (44837870081487/100000000000000 : ℝ)^3347
        have hw : |(5410713903/10000000000 : ℝ)|=(5410713903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049008449/2000000000 : ℝ)|^4371 ≤ (10763349173773/25000000000000 : ℝ)^3347
        have hw : |(1049008449/2000000000 : ℝ)|=(1049008449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s4_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267405223/500000000 : ℝ)*x 0 + (-1035017857/5000000000 : ℝ)*x 1 + (2622521067/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267405223/500000000 : ℝ)^4371 ≤ (2208075042963/5000000000000 : ℝ)^3347 := by
    have hnat : (267405223 : ℕ)^4371*5000000000000^3347 ≤ 2208075042963^3347*500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267405223 500000000 2208075042963 5000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035017857/5000000000 : ℝ)^4371 ≤ (12785103612763/100000000000000 : ℝ)^3347 := by
    have hnat : (1035017857 : ℕ)^4371*100000000000000^3347 ≤ 12785103612763^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035017857 5000000000 12785103612763 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622521067/5000000000 : ℝ)^4371 ≤ (43053395505203/100000000000000 : ℝ)^3347 := by
    have hnat : (2622521067 : ℕ)^4371*100000000000000^3347 ≤ 43053395505203^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622521067 5000000000 43053395505203 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267405223/500000000 : ℝ), (-1035017857/5000000000 : ℝ), (2622521067/5000000000 : ℝ)] ![(2208075042963/5000000000000 : ℝ), (12785103612763/100000000000000 : ℝ), (43053395505203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267405223/500000000 : ℝ)|^4371 ≤ (2208075042963/5000000000000 : ℝ)^3347
        have hw : |(267405223/500000000 : ℝ)|=(267405223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035017857/5000000000 : ℝ)|^4371 ≤ (12785103612763/100000000000000 : ℝ)^3347
        have hw : |(-1035017857/5000000000 : ℝ)|=(1035017857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622521067/5000000000 : ℝ)|^4371 ≤ (43053395505203/100000000000000 : ℝ)^3347
        have hw : |(2622521067/5000000000 : ℝ)|=(2622521067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s4_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069620897/2000000000 : ℝ)*x 0 + (2622521137/5000000000 : ℝ)*x 1 + (-258754437/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069620897/2000000000 : ℝ)^4371 ≤ (44161501128853/100000000000000 : ℝ)^3347 := by
    have hnat : (1069620897 : ℕ)^4371*100000000000000^3347 ≤ 44161501128853^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069620897 2000000000 44161501128853 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622521137/5000000000 : ℝ)^4371 ≤ (10763349251491/25000000000000 : ℝ)^3347 := by
    have hnat : (2622521137 : ℕ)^4371*25000000000000^3347 ≤ 10763349251491^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622521137 5000000000 10763349251491 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258754437/1250000000 : ℝ)^4371 ≤ (12785101854403/100000000000000 : ℝ)^3347 := by
    have hnat : (258754437 : ℕ)^4371*100000000000000^3347 ≤ 12785101854403^3347*1250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258754437 1250000000 12785101854403 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069620897/2000000000 : ℝ), (2622521137/5000000000 : ℝ), (-258754437/1250000000 : ℝ)] ![(44161501128853/100000000000000 : ℝ), (10763349251491/25000000000000 : ℝ), (12785101854403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069620897/2000000000 : ℝ)|^4371 ≤ (44161501128853/100000000000000 : ℝ)^3347
        have hw : |(1069620897/2000000000 : ℝ)|=(1069620897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622521137/5000000000 : ℝ)|^4371 ≤ (10763349251491/25000000000000 : ℝ)^3347
        have hw : |(2622521137/5000000000 : ℝ)|=(2622521137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258754437/1250000000 : ℝ)|^4371 ≤ (12785101854403/100000000000000 : ℝ)^3347
        have hw : |(-258754437/1250000000 : ℝ)|=(258754437/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s4_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308788067/10000000000 : ℝ)*x 0 + (4134100619/10000000000 : ℝ)*x 1 + (4490142011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308788067/10000000000 : ℝ)^4371 ≤ (33303331994527/100000000000000 : ℝ)^3347 := by
    have hnat : (4308788067 : ℕ)^4371*100000000000000^3347 ≤ 33303331994527^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308788067 10000000000 33303331994527 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4134100619/10000000000 : ℝ)^4371 ≤ (15775549876921/50000000000000 : ℝ)^3347 := by
    have hnat : (4134100619 : ℕ)^4371*50000000000000^3347 ≤ 15775549876921^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134100619 10000000000 15775549876921 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490142011/10000000000 : ℝ)^4371 ≤ (17572784115123/50000000000000 : ℝ)^3347 := by
    have hnat : (4490142011 : ℕ)^4371*50000000000000^3347 ≤ 17572784115123^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490142011 10000000000 17572784115123 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308788067/10000000000 : ℝ), (4134100619/10000000000 : ℝ), (4490142011/10000000000 : ℝ)] ![(33303331994527/100000000000000 : ℝ), (15775549876921/50000000000000 : ℝ), (17572784115123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308788067/10000000000 : ℝ)|^4371 ≤ (33303331994527/100000000000000 : ℝ)^3347
        have hw : |(4308788067/10000000000 : ℝ)|=(4308788067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4134100619/10000000000 : ℝ)|^4371 ≤ (15775549876921/50000000000000 : ℝ)^3347
        have hw : |(4134100619/10000000000 : ℝ)|=(4134100619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490142011/10000000000 : ℝ)|^4371 ≤ (17572784115123/50000000000000 : ℝ)^3347
        have hw : |(4490142011/10000000000 : ℝ)|=(4490142011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s4_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1985660991/10000000000 : ℝ)*x 0 + (2622824827/5000000000 : ℝ)*x 1 + (5410103121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1985660991/10000000000 : ℝ)^4371 ≤ (6054415859879/50000000000000 : ℝ)^3347 := by
    have hnat : (1985660991 : ℕ)^4371*50000000000000^3347 ≤ 6054415859879^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1985660991 10000000000 6054415859879 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622824827/5000000000 : ℝ)^4371 ≤ (43059908066083/100000000000000 : ℝ)^3347 := by
    have hnat : (2622824827 : ℕ)^4371*100000000000000^3347 ≤ 43059908066083^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622824827 5000000000 43059908066083 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410103121/10000000000 : ℝ)^4371 ≤ (11207815047889/25000000000000 : ℝ)^3347 := by
    have hnat : (5410103121 : ℕ)^4371*25000000000000^3347 ≤ 11207815047889^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410103121 10000000000 11207815047889 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1985660991/10000000000 : ℝ), (2622824827/5000000000 : ℝ), (5410103121/10000000000 : ℝ)] ![(6054415859879/50000000000000 : ℝ), (43059908066083/100000000000000 : ℝ), (11207815047889/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1985660991/10000000000 : ℝ)|^4371 ≤ (6054415859879/50000000000000 : ℝ)^3347
        have hw : |(-1985660991/10000000000 : ℝ)|=(1985660991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622824827/5000000000 : ℝ)|^4371 ≤ (43059908066083/100000000000000 : ℝ)^3347
        have hw : |(2622824827/5000000000 : ℝ)|=(2622824827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410103121/10000000000 : ℝ)|^4371 ≤ (11207815047889/25000000000000 : ℝ)^3347
        have hw : |(5410103121/10000000000 : ℝ)|=(5410103121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s4_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305111249/10000000000 : ℝ)*x 0 + (-1904974733/10000000000 : ℝ)*x 1 + (5410103381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305111249/10000000000 : ℝ)^4371 ≤ (43698444852073/100000000000000 : ℝ)^3347 := by
    have hnat : (5305111249 : ℕ)^4371*100000000000000^3347 ≤ 43698444852073^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305111249 10000000000 43698444852073 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1904974733/10000000000 : ℝ)^4371 ≤ (11470292119553/100000000000000 : ℝ)^3347 := by
    have hnat : (1904974733 : ℕ)^4371*100000000000000^3347 ≤ 11470292119553^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904974733 10000000000 11470292119553 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410103381/10000000000 : ℝ)^4371 ≤ (4483126300523/10000000000000 : ℝ)^3347 := by
    have hnat : (5410103381 : ℕ)^4371*10000000000000^3347 ≤ 4483126300523^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410103381 10000000000 4483126300523 10000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305111249/10000000000 : ℝ), (-1904974733/10000000000 : ℝ), (5410103381/10000000000 : ℝ)] ![(43698444852073/100000000000000 : ℝ), (11470292119553/100000000000000 : ℝ), (4483126300523/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305111249/10000000000 : ℝ)|^4371 ≤ (43698444852073/100000000000000 : ℝ)^3347
        have hw : |(5305111249/10000000000 : ℝ)|=(5305111249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1904974733/10000000000 : ℝ)|^4371 ≤ (11470292119553/100000000000000 : ℝ)^3347
        have hw : |(-1904974733/10000000000 : ℝ)|=(1904974733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410103381/10000000000 : ℝ)|^4371 ≤ (4483126300523/10000000000000 : ℝ)^3347
        have hw : |(5410103381/10000000000 : ℝ)|=(5410103381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s4_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132627781/250000000 : ℝ)*x 0 + (5410103219/10000000000 : ℝ)*x 1 + (-1904974969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132627781/250000000 : ℝ)^4371 ≤ (43698444755259/100000000000000 : ℝ)^3347 := by
    have hnat : (132627781 : ℕ)^4371*100000000000000^3347 ≤ 43698444755259^3347*250000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132627781 250000000 43698444755259 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5410103219/10000000000 : ℝ)^4371 ≤ (8966252250419/20000000000000 : ℝ)^3347 := by
    have hnat : (5410103219 : ℕ)^4371*20000000000000^3347 ≤ 8966252250419^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410103219 10000000000 8966252250419 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904974969/10000000000 : ℝ)^4371 ≤ (2294058795063/20000000000000 : ℝ)^3347 := by
    have hnat : (1904974969 : ℕ)^4371*20000000000000^3347 ≤ 2294058795063^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904974969 10000000000 2294058795063 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132627781/250000000 : ℝ), (5410103219/10000000000 : ℝ), (-1904974969/10000000000 : ℝ)] ![(43698444755259/100000000000000 : ℝ), (8966252250419/20000000000000 : ℝ), (2294058795063/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132627781/250000000 : ℝ)|^4371 ≤ (43698444755259/100000000000000 : ℝ)^3347
        have hw : |(132627781/250000000 : ℝ)|=(132627781/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5410103219/10000000000 : ℝ)|^4371 ≤ (8966252250419/20000000000000 : ℝ)^3347
        have hw : |(5410103219/10000000000 : ℝ)|=(5410103219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1904974969/10000000000 : ℝ)|^4371 ≤ (2294058795063/20000000000000 : ℝ)^3347
        have hw : |(-1904974969/10000000000 : ℝ)|=(1904974969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s4_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2154406843/5000000000 : ℝ)*x 0 + (897767257/2000000000 : ℝ)*x 1 + (4135413701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154406843/5000000000 : ℝ)^4371 ≤ (16651795294791/50000000000000 : ℝ)^3347 := by
    have hnat : (2154406843 : ℕ)^4371*50000000000000^3347 ≤ 16651795294791^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154406843 5000000000 16651795294791 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (897767257/2000000000 : ℝ)^4371 ≤ (54894096409/156250000000 : ℝ)^3347 := by
    have hnat : (897767257 : ℕ)^4371*156250000000^3347 ≤ 54894096409^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897767257 2000000000 54894096409 156250000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4135413701/10000000000 : ℝ)^4371 ≤ (31564187700023/100000000000000 : ℝ)^3347 := by
    have hnat : (4135413701 : ℕ)^4371*100000000000000^3347 ≤ 31564187700023^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4135413701 10000000000 31564187700023 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154406843/5000000000 : ℝ), (897767257/2000000000 : ℝ), (4135413701/10000000000 : ℝ)] ![(16651795294791/50000000000000 : ℝ), (54894096409/156250000000 : ℝ), (31564187700023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154406843/5000000000 : ℝ)|^4371 ≤ (16651795294791/50000000000000 : ℝ)^3347
        have hw : |(2154406843/5000000000 : ℝ)|=(2154406843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(897767257/2000000000 : ℝ)|^4371 ≤ (54894096409/156250000000 : ℝ)^3347
        have hw : |(897767257/2000000000 : ℝ)|=(897767257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4135413701/10000000000 : ℝ)|^4371 ≤ (31564187700023/100000000000000 : ℝ)^3347
        have hw : |(4135413701/10000000000 : ℝ)|=(4135413701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1409/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (739/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14957/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14957/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5553/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14957/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14957/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5553/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14957/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14957/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5553/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5553/50000 : ℝ) ^ (2185/512 : ℝ) ≤ (8449729131673411/100000000000000000000 : ℝ) := by
    have hpowers : (5553/50000 : ℝ)^2185 ≤ (8449729131673411/100000000000000000000 : ℝ)^512 := by
      have hnat : (5553 : ℕ)^2185*100000000000000000000^512 ≤ 8449729131673411^512*50000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5553 50000 8449729131673411 100000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5553/50000 : ℝ)) (X := (8449729131673411/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14957/100000 : ℝ) ^ (2185/512 : ℝ) ≤ (15050620865487341/50000000000000000000 : ℝ) := by
    have hpowers : (14957/100000 : ℝ)^2185 ≤ (15050620865487341/50000000000000000000 : ℝ)^512 := by
      have hnat : (14957 : ℕ)^2185*50000000000000000000^512 ≤ 15050620865487341^512*100000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14957 100000 15050620865487341 50000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14957/100000 : ℝ)) (X := (15050620865487341/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008449729131673411/50000000000000000000 : ℝ) ≤ (10000395970841657/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (50008449729131673411/50000000000000000000 : ℝ)^512 ≤ (10000395970841657/10000000000000000 : ℝ)^2185 := by
      have hnat : (50008449729131673411 : ℕ)^512*10000000000000000^2185 ≤ 10000395970841657^2185*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008449729131673411 50000000000000000000 10000395970841657 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000395970841657/10000000000000000 : ℝ)) (X := (50008449729131673411/50000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038550970862648093/100000000000000000000 : ℝ) ≤ (10000903212111873/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (100038550970862648093/100000000000000000000 : ℝ)^512 ≤ (10000903212111873/10000000000000000 : ℝ)^2185 := by
      have hnat : (100038550970862648093 : ℕ)^512*10000000000000000^2185 ≤ 10000903212111873^2185*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038550970862648093 100000000000000000000 10000903212111873 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000903212111873/10000000000000000 : ℝ)) (X := (100038550970862648093/100000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015050620865487341/25000000000000000000 : ℝ) ≤ (10001410453382089/10000000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (25015050620865487341/25000000000000000000 : ℝ)^512 ≤ (10001410453382089/10000000000000000 : ℝ)^2185 := by
      have hnat : (25015050620865487341 : ℕ)^512*10000000000000000^2185 ≤ 10001410453382089^2185*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015050620865487341 25000000000000000000 10001410453382089 10000000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001410453382089/10000000000000000 : ℝ)) (X := (25015050620865487341/25000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8449729131673411/100000000000000000000 : ℝ) ≤ ((7700051608123436663/7702000000000000000 : ℝ)+2*(63405158777/48137500000000 : ℝ)*(5553/50000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (7700051608123436663/7702000000000000000 : ℝ)+2*(63405158777/48137500000000 : ℝ)*(5553/50000 : ℝ)=(10000395970841657/10000000000000000 : ℝ) by norm_num, show 1+2*(8449729131673411/100000000000000000000 : ℝ)=(50008449729131673411/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15050620865487341/50000000000000000000 : ℝ)+(8449729131673411/100000000000000000000 : ℝ) ≤ ((7700051608123436663/7702000000000000000 : ℝ)+(63405158777/48137500000000 : ℝ)*((14957/100000 : ℝ)+(5553/50000 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (7700051608123436663/7702000000000000000 : ℝ)+(63405158777/48137500000000 : ℝ)*((14957/100000 : ℝ)+(5553/50000 : ℝ))=(10000903212111873/10000000000000000 : ℝ) by norm_num, show 1+(15050620865487341/50000000000000000000 : ℝ)+(8449729131673411/100000000000000000000 : ℝ)=(100038550970862648093/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15050620865487341/50000000000000000000 : ℝ) ≤ ((7700051608123436663/7702000000000000000 : ℝ)+2*(63405158777/48137500000000 : ℝ)*(14957/100000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (7700051608123436663/7702000000000000000 : ℝ)+2*(63405158777/48137500000000 : ℝ)*(14957/100000 : ℝ)=(10001410453382089/10000000000000000 : ℝ) by norm_num, show 1+2*(15050620865487341/50000000000000000000 : ℝ)=(25015050620865487341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7700051608123436663/7702000000000000000 : ℝ)*(X 1 0+X 2 0)+(63405158777/48137500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5553/50000 : ℝ)) (hi := (14957/100000 : ℝ)) (c := (7700051608123436663/7702000000000000000 : ℝ)) (alpha := (63405158777/48137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7700051608123436663/7702000000000000000 : ℝ)*(X 0 1+X 2 1)+(63405158777/48137500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5553/50000 : ℝ)) (hi := (14957/100000 : ℝ)) (c := (7700051608123436663/7702000000000000000 : ℝ)) (alpha := (63405158777/48137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7700051608123436663/7702000000000000000 : ℝ)*(X 0 2+X 1 2)+(63405158777/48137500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (5553/50000 : ℝ)) (hi := (14957/100000 : ℝ)) (c := (7700051608123436663/7702000000000000000 : ℝ)) (alpha := (63405158777/48137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1985648621/10000000000 : ℝ)*X 0 0+(5410713903/10000000000 : ℝ)*X 0 1+(1049008449/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267405223/500000000 : ℝ)*X 1 0+(-1035017857/5000000000 : ℝ)*X 1 1+(2622521067/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069620897/2000000000 : ℝ)*X 2 0+(2622521137/5000000000 : ℝ)*X 2 1+(-258754437/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308788067/10000000000 : ℝ)*X 0 0+(4134100619/10000000000 : ℝ)*X 0 1+(4490142011/10000000000 : ℝ)*X 0 2+(4308788067/10000000000 : ℝ)*X 1 0+(4134100619/10000000000 : ℝ)*X 1 1+(4490142011/10000000000 : ℝ)*X 1 2+(4308788067/10000000000 : ℝ)*X 2 0+(4134100619/10000000000 : ℝ)*X 2 1+(4490142011/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1985660991/10000000000 : ℝ)*X 0 0+(2622824827/5000000000 : ℝ)*X 0 1+(5410103121/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305111249/10000000000 : ℝ)*X 1 0+(-1904974733/10000000000 : ℝ)*X 1 1+(5410103381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132627781/250000000 : ℝ)*X 2 0+(5410103219/10000000000 : ℝ)*X 2 1+(-1904974969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2154406843/5000000000 : ℝ)*X 0 0+(897767257/2000000000 : ℝ)*X 0 1+(4135413701/10000000000 : ℝ)*X 0 2+(2154406843/5000000000 : ℝ)*X 1 0+(897767257/2000000000 : ℝ)*X 1 1+(4135413701/10000000000 : ℝ)*X 1 2+(2154406843/5000000000 : ℝ)*X 2 0+(897767257/2000000000 : ℝ)*X 2 1+(4135413701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10209108070119737773821/3851000000000000000000000000 : ℝ) := by norm_num
    linear_combination (975139037/100000000000000 : ℝ)*(base19) + (145825967/20000000000000 : ℝ)*(base23) + (14665847/10000000000000 : ℝ)*(lower2) + (33098077/100000000000000 : ℝ)*(upper3) + (54458183/50000000000000 : ℝ)*(upper5) + (442237812730791/10000000000000 : ℝ)*(major0) + (442237812730791/10000000000000 : ℝ)*(major1) + (442237812730791/10000000000000 : ℝ)*(major2) + (754506346737897/12500000000000 : ℝ)*(sp0) + (3018035912773807/50000000000000 : ℝ)*(sp1) + (1207214414311363/20000000000000 : ℝ)*(sp2) + (702168169093057/25000000000000 : ℝ)*(sp3) + (11013391737/50000000000000 : ℝ)*(sp4) + (10689189341/100000000000000 : ℝ)*(sp7) + (280868336556157/10000000000000 : ℝ)*(f.failure) + (120721456013733/2000000000000 : ℝ)*(f.sum) + (396739489417/192550000000000000000000000 : ℝ)*base65 + (52436120193690433/77020000000000000000000000000000 : ℝ)*base67 + (26486488075949567/77020000000000000000000000000000 : ℝ)*base70 + (952024991088670433/77020000000000000000000000000000 : ℝ)*base71 + (11353631534941/3851000000000000000000000000 : ℝ)*base73 + (1036594222345989567/77020000000000000000000000000000 : ℝ)*base76 + (423817453656970433/77020000000000000000000000000000 : ℝ)*base77 + (300910334996029567/77020000000000000000000000000000 : ℝ)*base80 + (9297607774247/3851000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (96173/50000000000000000000 : ℝ)*base89 + (96173/50000000000000000000 : ℝ)*base91 + (96173/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (744525858402484207874248389/192550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (296626753/100000000000000 : ℝ)*(base19) + (11178381/2500000000000 : ℝ)*(base23) + (117402261/100000000000000 : ℝ)*(upper2) + (1958169/4000000000000 : ℝ)*(upper3) + (74175607/50000000000000 : ℝ)*(upper5) + (4455109655045601/100000000000000 : ℝ)*(major0) + (4455109655045601/100000000000000 : ℝ)*(major1) + (4455109655045601/100000000000000 : ℝ)*(major2) + (2972155309/20000000000000 : ℝ)*(sp1) + (7398392121/100000000000000 : ℝ)*(sp2) + (6080747792807961/100000000000000 : ℝ)*(sp4) + (6080732635404663/100000000000000 : ℝ)*(sp5) + (30403699736403/500000000000 : ℝ)*(sp6) + (2829471388394487/100000000000000 : ℝ)*(sp7) + (2829471388394487/100000000000000 : ℝ)*(f.failure) + (6080747792807961/100000000000000 : ℝ)*(f.sum) + (87980104700589/19255000000000000000000000000 : ℝ)*base66 + (4979678346708789463/770200000000000000000000000000000 : ℝ)*base67 + (6554187096397010537/770200000000000000000000000000000 : ℝ)*base70 + (3139259857407210537/770200000000000000000000000000000 : ℝ)*base72 + (29852362825443/9627500000000000000000000000 : ℝ)*base73 + (5725194920707410537/770200000000000000000000000000000 : ℝ)*base76 + (3044110811246810537/770200000000000000000000000000000 : ℝ)*base78 + (6050878865303210537/770200000000000000000000000000000 : ℝ)*base80 + (66338221011789/19255000000000000000000000000 : ℝ)*base82 + (465543/500000000000000000000 : ℝ)*base89 + (465543/500000000000000000000 : ℝ)*base91 + (465543/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1411_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14957/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5553/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (739/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1411_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1411_s5_0 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-992902183/5000000000 : ℝ)*x 0 + (1352339291/2500000000 : ℝ)*x 1 + (5246296149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (992902183/5000000000 : ℝ)^4371 ≤ (12109973547161/100000000000000 : ℝ)^3347 := by
    have hnat : (992902183 : ℕ)^4371*100000000000000^3347 ≤ 12109973547161^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992902183 5000000000 12109973547161 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352339291/2500000000 : ℝ)^4371 ≤ (44823187745883/100000000000000 : ℝ)^3347 := by
    have hnat : (1352339291 : ℕ)^4371*100000000000000^3347 ≤ 44823187745883^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352339291 2500000000 44823187745883 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246296149/10000000000 : ℝ)^4371 ≤ (43066838688973/100000000000000 : ℝ)^3347 := by
    have hnat : (5246296149 : ℕ)^4371*100000000000000^3347 ≤ 43066838688973^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246296149 10000000000 43066838688973 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-992902183/5000000000 : ℝ), (1352339291/2500000000 : ℝ), (5246296149/10000000000 : ℝ)] ![(12109973547161/100000000000000 : ℝ), (44823187745883/100000000000000 : ℝ), (43066838688973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-992902183/5000000000 : ℝ)|^4371 ≤ (12109973547161/100000000000000 : ℝ)^3347
        have hw : |(-992902183/5000000000 : ℝ)|=(992902183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352339291/2500000000 : ℝ)|^4371 ≤ (44823187745883/100000000000000 : ℝ)^3347
        have hw : |(1352339291/2500000000 : ℝ)|=(1352339291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246296149/10000000000 : ℝ)|^4371 ≤ (43066838688973/100000000000000 : ℝ)^3347
        have hw : |(5246296149/10000000000 : ℝ)|=(5246296149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s5_1 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069550763/2000000000 : ℝ)*x 0 + (-64651173/312500000 : ℝ)*x 1 + (5246296293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069550763/2000000000 : ℝ)^4371 ≤ (44157719635901/100000000000000 : ℝ)^3347 := by
    have hnat : (1069550763 : ℕ)^4371*100000000000000^3347 ≤ 44157719635901^3347*2000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069550763 2000000000 44157719635901 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64651173/312500000 : ℝ)^4371 ≤ (3193860028541/25000000000000 : ℝ)^3347 := by
    have hnat : (64651173 : ℕ)^4371*25000000000000^3347 ≤ 3193860028541^3347*312500000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64651173 312500000 3193860028541 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246296293/10000000000 : ℝ)^4371 ≤ (21533420116363/50000000000000 : ℝ)^3347 := by
    have hnat : (5246296293 : ℕ)^4371*50000000000000^3347 ≤ 21533420116363^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246296293 10000000000 21533420116363 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069550763/2000000000 : ℝ), (-64651173/312500000 : ℝ), (5246296293/10000000000 : ℝ)] ![(44157719635901/100000000000000 : ℝ), (3193860028541/25000000000000 : ℝ), (21533420116363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069550763/2000000000 : ℝ)|^4371 ≤ (44157719635901/100000000000000 : ℝ)^3347
        have hw : |(1069550763/2000000000 : ℝ)|=(1069550763/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64651173/312500000 : ℝ)|^4371 ≤ (3193860028541/25000000000000 : ℝ)^3347
        have hw : |(-64651173/312500000 : ℝ)|=(64651173/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246296293/10000000000 : ℝ)|^4371 ≤ (21533420116363/50000000000000 : ℝ)^3347
        have hw : |(5246296293/10000000000 : ℝ)|=(5246296293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s5_2 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673876913/5000000000 : ℝ)*x 0 + (2623148093/5000000000 : ℝ)*x 1 + (-2068837663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673876913/5000000000 : ℝ)^4371 ≤ (1103942993863/2500000000000 : ℝ)^3347 := by
    have hnat : (2673876913 : ℕ)^4371*2500000000000^3347 ≤ 1103942993863^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673876913 5000000000 1103942993863 2500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623148093/5000000000 : ℝ)^4371 ≤ (672919360713/1562500000000 : ℝ)^3347 := by
    have hnat : (2623148093 : ℕ)^4371*1562500000000^3347 ≤ 672919360713^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623148093 5000000000 672919360713 1562500000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2068837663/10000000000 : ℝ)^4371 ≤ (12775441138349/100000000000000 : ℝ)^3347 := by
    have hnat : (2068837663 : ℕ)^4371*100000000000000^3347 ≤ 12775441138349^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068837663 10000000000 12775441138349 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673876913/5000000000 : ℝ), (2623148093/5000000000 : ℝ), (-2068837663/10000000000 : ℝ)] ![(1103942993863/2500000000000 : ℝ), (672919360713/1562500000000 : ℝ), (12775441138349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673876913/5000000000 : ℝ)|^4371 ≤ (1103942993863/2500000000000 : ℝ)^3347
        have hw : |(2673876913/5000000000 : ℝ)|=(2673876913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623148093/5000000000 : ℝ)|^4371 ≤ (672919360713/1562500000000 : ℝ)^3347
        have hw : |(2623148093/5000000000 : ℝ)|=(2623148093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2068837663/10000000000 : ℝ)|^4371 ≤ (12775441138349/100000000000000 : ℝ)^3347
        have hw : |(-2068837663/10000000000 : ℝ)|=(2068837663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s5_3 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4308880653/10000000000 : ℝ)*x 0 + (1034223777/2500000000 : ℝ)*x 1 + (1121831323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4308880653/10000000000 : ℝ)^4371 ≤ (16652133274259/50000000000000 : ℝ)^3347 := by
    have hnat : (4308880653 : ℕ)^4371*50000000000000^3347 ≤ 16652133274259^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4308880653 10000000000 16652133274259 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1034223777/2500000000 : ℝ)^4371 ≤ (31578954926577/100000000000000 : ℝ)^3347 := by
    have hnat : (1034223777 : ℕ)^4371*100000000000000^3347 ≤ 31578954926577^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034223777 2500000000 31578954926577 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121831323/2500000000 : ℝ)^4371 ≤ (4389597313903/12500000000000 : ℝ)^3347 := by
    have hnat : (1121831323 : ℕ)^4371*12500000000000^3347 ≤ 4389597313903^3347*2500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121831323 2500000000 4389597313903 12500000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4308880653/10000000000 : ℝ), (1034223777/2500000000 : ℝ), (1121831323/2500000000 : ℝ)] ![(16652133274259/50000000000000 : ℝ), (31578954926577/100000000000000 : ℝ), (4389597313903/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4308880653/10000000000 : ℝ)|^4371 ≤ (16652133274259/50000000000000 : ℝ)^3347
        have hw : |(4308880653/10000000000 : ℝ)|=(4308880653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1034223777/2500000000 : ℝ)|^4371 ≤ (31578954926577/100000000000000 : ℝ)^3347
        have hw : |(1034223777/2500000000 : ℝ)|=(1034223777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121831323/2500000000 : ℝ)|^4371 ≤ (4389597313903/12500000000000 : ℝ)^3347
        have hw : |(1121831323/2500000000 : ℝ)|=(1121831323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s5_4 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-99290797/500000000 : ℝ)*x 0 + (5246884813/10000000000 : ℝ)*x 1 + (5408765449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (99290797/500000000 : ℝ)^4371 ≤ (6055032861351/50000000000000 : ℝ)^3347 := by
    have hnat : (99290797 : ℕ)^4371*50000000000000^3347 ≤ 6055032861351^3347*500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99290797 500000000 6055032861351 50000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246884813/10000000000 : ℝ)^4371 ≤ (43073149573251/100000000000000 : ℝ)^3347 := by
    have hnat : (5246884813 : ℕ)^4371*100000000000000^3347 ≤ 43073149573251^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246884813 10000000000 43073149573251 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408765449/10000000000 : ℝ)^4371 ≤ (44816784687121/100000000000000 : ℝ)^3347 := by
    have hnat : (5408765449 : ℕ)^4371*100000000000000^3347 ≤ 44816784687121^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408765449 10000000000 44816784687121 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-99290797/500000000 : ℝ), (5246884813/10000000000 : ℝ), (5408765449/10000000000 : ℝ)] ![(6055032861351/50000000000000 : ℝ), (43073149573251/100000000000000 : ℝ), (44816784687121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-99290797/500000000 : ℝ)|^4371 ≤ (6055032861351/50000000000000 : ℝ)^3347
        have hw : |(-99290797/500000000 : ℝ)|=(99290797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246884813/10000000000 : ℝ)|^4371 ≤ (43073149573251/100000000000000 : ℝ)^3347
        have hw : |(5246884813/10000000000 : ℝ)|=(5246884813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408765449/10000000000 : ℝ)|^4371 ≤ (44816784687121/100000000000000 : ℝ)^3347
        have hw : |(5408765449/10000000000 : ℝ)|=(5408765449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s5_5 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331589897/625000000 : ℝ)*x 0 + (-953184163/5000000000 : ℝ)*x 1 + (5408765449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331589897/625000000 : ℝ)^4371 ≤ (10925490894019/25000000000000 : ℝ)^3347 := by
    have hnat : (331589897 : ℕ)^4371*25000000000000^3347 ≤ 10925490894019^3347*625000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331589897 625000000 10925490894019 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (953184163/5000000000 : ℝ)^4371 ≤ (2296250344897/20000000000000 : ℝ)^3347 := by
    have hnat : (953184163 : ℕ)^4371*20000000000000^3347 ≤ 2296250344897^3347*5000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953184163 5000000000 2296250344897 20000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5408765449/10000000000 : ℝ)^4371 ≤ (44816784687121/100000000000000 : ℝ)^3347 := by
    have hnat : (5408765449 : ℕ)^4371*100000000000000^3347 ≤ 44816784687121^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408765449 10000000000 44816784687121 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331589897/625000000 : ℝ), (-953184163/5000000000 : ℝ), (5408765449/10000000000 : ℝ)] ![(10925490894019/25000000000000 : ℝ), (2296250344897/20000000000000 : ℝ), (44816784687121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331589897/625000000 : ℝ)|^4371 ≤ (10925490894019/25000000000000 : ℝ)^3347
        have hw : |(331589897/625000000 : ℝ)|=(331589897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-953184163/5000000000 : ℝ)|^4371 ≤ (2296250344897/20000000000000 : ℝ)^3347
        have hw : |(-953184163/5000000000 : ℝ)|=(953184163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5408765449/10000000000 : ℝ)|^4371 ≤ (44816784687121/100000000000000 : ℝ)^3347
        have hw : |(5408765449/10000000000 : ℝ)|=(5408765449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s5_6 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106108767/200000000 : ℝ)*x 0 + (5408765451/10000000000 : ℝ)*x 1 + (-76254733/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106108767/200000000 : ℝ)^4371 ≤ (43701963554561/100000000000000 : ℝ)^3347 := by
    have hnat : (106108767 : ℕ)^4371*100000000000000^3347 ≤ 43701963554561^3347*200000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106108767 200000000 43701963554561 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408765451/10000000000 : ℝ)^4371 ≤ (44816784708763/100000000000000 : ℝ)^3347 := by
    have hnat : (5408765451 : ℕ)^4371*100000000000000^3347 ≤ 44816784708763^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408765451 10000000000 44816784708763 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76254733/400000000 : ℝ)^4371 ≤ (574062585831/5000000000000 : ℝ)^3347 := by
    have hnat : (76254733 : ℕ)^4371*5000000000000^3347 ≤ 574062585831^3347*400000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76254733 400000000 574062585831 5000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106108767/200000000 : ℝ), (5408765451/10000000000 : ℝ), (-76254733/400000000 : ℝ)] ![(43701963554561/100000000000000 : ℝ), (44816784708763/100000000000000 : ℝ), (574062585831/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106108767/200000000 : ℝ)|^4371 ≤ (43701963554561/100000000000000 : ℝ)^3347
        have hw : |(106108767/200000000 : ℝ)|=(106108767/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408765451/10000000000 : ℝ)|^4371 ≤ (44816784708763/100000000000000 : ℝ)^3347
        have hw : |(5408765451/10000000000 : ℝ)|=(5408765451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76254733/400000000 : ℝ)|^4371 ≤ (574062585831/5000000000000 : ℝ)^3347
        have hw : |(-76254733/400000000 : ℝ)|=(76254733/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1411_s5_7 (p : ℝ) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (67326649/156250000 : ℝ)*x 0 + (224303017/500000000 : ℝ)*x 1 + (4138166611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (67326649/156250000 : ℝ)^4371 ≤ (8326129429031/25000000000000 : ℝ)^3347 := by
    have hnat : (67326649 : ℕ)^4371*25000000000000^3347 ≤ 8326129429031^3347*156250000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67326649 156250000 8326129429031 25000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224303017/500000000 : ℝ)^4371 ≤ (35103851220197/100000000000000 : ℝ)^3347 := by
    have hnat : (224303017 : ℕ)^4371*100000000000000^3347 ≤ 35103851220197^3347*500000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224303017 500000000 35103851220197 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4138166611/10000000000 : ℝ)^4371 ≤ (31591631040823/100000000000000 : ℝ)^3347 := by
    have hnat : (4138166611 : ℕ)^4371*100000000000000^3347 ≤ 31591631040823^3347*10000000000^4371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138166611 10000000000 31591631040823 100000000000000 4371 3347 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4371/1024 : ℝ)) 4371 3347 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(67326649/156250000 : ℝ), (224303017/500000000 : ℝ), (4138166611/10000000000 : ℝ)] ![(8326129429031/25000000000000 : ℝ), (35103851220197/100000000000000 : ℝ), (31591631040823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(67326649/156250000 : ℝ)|^4371 ≤ (8326129429031/25000000000000 : ℝ)^3347
        have hw : |(67326649/156250000 : ℝ)|=(67326649/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224303017/500000000 : ℝ)|^4371 ≤ (35103851220197/100000000000000 : ℝ)^3347
        have hw : |(224303017/500000000 : ℝ)|=(224303017/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4138166611/10000000000 : ℝ)|^4371 ≤ (31591631040823/100000000000000 : ℝ)^3347
        have hw : |(4138166611/10000000000 : ℝ)|=(4138166611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1411_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (739/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (5649/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (739/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (739/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1409/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (739/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (739/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1409/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (739/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (739/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1409/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1409/12500 : ℝ) ^ (2185/512 : ℝ) ≤ (900202304022733/10000000000000000000 : ℝ) := by
    have hpowers : (1409/12500 : ℝ)^2185 ≤ (900202304022733/10000000000000000000 : ℝ)^512 := by
      have hnat : (1409 : ℕ)^2185*10000000000000000000^512 ≤ 900202304022733^512*12500^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 12500 900202304022733 10000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/12500 : ℝ)) (X := (900202304022733/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hpowhi : (739/5000 : ℝ) ^ (2185/512 : ℝ) ≤ (28610192384811367/100000000000000000000 : ℝ) := by
    have hpowers : (739/5000 : ℝ)^2185 ≤ (28610192384811367/100000000000000000000 : ℝ)^512 := by
      have hnat : (739 : ℕ)^2185*100000000000000000000^512 ≤ 28610192384811367^512*5000^2185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        739 5000 28610192384811367 100000000000000000000 2185 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (739/5000 : ℝ)) (X := (28610192384811367/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000900202304022733/5000000000000000000 : ℝ) ≤ (125005273132891/125000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (5000900202304022733/5000000000000000000 : ℝ)^512 ≤ (125005273132891/125000000000000 : ℝ)^2185 := by
      have hnat : (5000900202304022733 : ℕ)^512*125000000000000^2185 ≤ 125005273132891^2185*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000900202304022733 5000000000000000000 125005273132891 125000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125005273132891/125000000000000 : ℝ)) (X := (5000900202304022733/5000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037612215425038697/100000000000000000000 : ℝ) ≤ (125011015264279/125000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (100037612215425038697/100000000000000000000 : ℝ)^512 ≤ (125011015264279/125000000000000 : ℝ)^2185 := by
      have hnat : (100037612215425038697 : ℕ)^512*125000000000000^2185 ≤ 125011015264279^2185*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037612215425038697 100000000000000000000 125011015264279 125000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125011015264279/125000000000000 : ℝ)) (X := (100037612215425038697/100000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028610192384811367/50000000000000000000 : ℝ) ≤ (125016757395667/125000000000000 : ℝ) ^ (2185/512 : ℝ) := by
    have hpowers : (50028610192384811367/50000000000000000000 : ℝ)^512 ≤ (125016757395667/125000000000000 : ℝ)^2185 := by
      have hnat : (50028610192384811367 : ℕ)^512*125000000000000^2185 ≤ 125016757395667^2185*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028610192384811367 50000000000000000000 125016757395667 125000000000000 512 2185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125016757395667/125000000000000 : ℝ)) (X := (50028610192384811367/50000000000000000000 : ℝ)) (by norm_num) 2185 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(900202304022733/10000000000000000000 : ℝ) ≤ ((109597261885042639/109625000000000000 : ℝ)+2*(1435532847/1096250000000 : ℝ)*(1409/12500 : ℝ))^(2185/512 : ℝ) := by
    rw [show (109597261885042639/109625000000000000 : ℝ)+2*(1435532847/1096250000000 : ℝ)*(1409/12500 : ℝ)=(125005273132891/125000000000000 : ℝ) by norm_num, show 1+2*(900202304022733/10000000000000000000 : ℝ)=(5000900202304022733/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28610192384811367/100000000000000000000 : ℝ)+(900202304022733/10000000000000000000 : ℝ) ≤ ((109597261885042639/109625000000000000 : ℝ)+(1435532847/1096250000000 : ℝ)*((739/5000 : ℝ)+(1409/12500 : ℝ)))^(2185/512 : ℝ) := by
    rw [show (109597261885042639/109625000000000000 : ℝ)+(1435532847/1096250000000 : ℝ)*((739/5000 : ℝ)+(1409/12500 : ℝ))=(125011015264279/125000000000000 : ℝ) by norm_num, show 1+(28610192384811367/100000000000000000000 : ℝ)+(900202304022733/10000000000000000000 : ℝ)=(100037612215425038697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28610192384811367/100000000000000000000 : ℝ) ≤ ((109597261885042639/109625000000000000 : ℝ)+2*(1435532847/1096250000000 : ℝ)*(739/5000 : ℝ))^(2185/512 : ℝ) := by
    rw [show (109597261885042639/109625000000000000 : ℝ)+2*(1435532847/1096250000000 : ℝ)*(739/5000 : ℝ)=(125016757395667/125000000000000 : ℝ) by norm_num, show 1+2*(28610192384811367/100000000000000000000 : ℝ)=(50028610192384811367/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (109597261885042639/109625000000000000 : ℝ)*(X 1 0+X 2 0)+(1435532847/1096250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (739/5000 : ℝ)) (c := (109597261885042639/109625000000000000 : ℝ)) (alpha := (1435532847/1096250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (109597261885042639/109625000000000000 : ℝ)*(X 0 1+X 2 1)+(1435532847/1096250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (739/5000 : ℝ)) (c := (109597261885042639/109625000000000000 : ℝ)) (alpha := (1435532847/1096250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (109597261885042639/109625000000000000 : ℝ)*(X 0 2+X 1 2)+(1435532847/1096250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2185/512 : ℝ)) (lo := (1409/12500 : ℝ)) (hi := (739/5000 : ℝ)) (c := (109597261885042639/109625000000000000 : ℝ)) (alpha := (1435532847/1096250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-992902183/5000000000 : ℝ)*X 0 0+(1352339291/2500000000 : ℝ)*X 0 1+(5246296149/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069550763/2000000000 : ℝ)*X 1 0+(-64651173/312500000 : ℝ)*X 1 1+(5246296293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673876913/5000000000 : ℝ)*X 2 0+(2623148093/5000000000 : ℝ)*X 2 1+(-2068837663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4308880653/10000000000 : ℝ)*X 0 0+(1034223777/2500000000 : ℝ)*X 0 1+(1121831323/2500000000 : ℝ)*X 0 2+(4308880653/10000000000 : ℝ)*X 1 0+(1034223777/2500000000 : ℝ)*X 1 1+(1121831323/2500000000 : ℝ)*X 1 2+(4308880653/10000000000 : ℝ)*X 2 0+(1034223777/2500000000 : ℝ)*X 2 1+(1121831323/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-99290797/500000000 : ℝ)*X 0 0+(5246884813/10000000000 : ℝ)*X 0 1+(5408765449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331589897/625000000 : ℝ)*X 1 0+(-953184163/5000000000 : ℝ)*X 1 1+(5408765449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((106108767/200000000 : ℝ)*X 2 0+(5408765451/10000000000 : ℝ)*X 2 1+(-76254733/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((67326649/156250000 : ℝ)*X 0 0+(224303017/500000000 : ℝ)*X 0 1+(4138166611/10000000000 : ℝ)*X 0 2+(67326649/156250000 : ℝ)*X 1 0+(224303017/500000000 : ℝ)*X 1 1+(4138166611/10000000000 : ℝ)*X 1 2+(67326649/156250000 : ℝ)*X 2 0+(224303017/500000000 : ℝ)*X 2 1+(4138166611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1411_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3924765791818789738242609/342578125000000000000000000000 : ℝ) := by norm_num
    linear_combination (1945536027/100000000000000 : ℝ)*(base19) + (227961873/12500000000000 : ℝ)*(base23) + (575229/800000000000 : ℝ)*(lower2) + (181126049/50000000000000 : ℝ)*(upper3) + (26455961/25000000000000 : ℝ)*(upper5) + (4493218252958983/100000000000000 : ℝ)*(major0) + (4493218252958983/100000000000000 : ℝ)*(major1) + (561652281619873/12500000000000 : ℝ)*(major2) + (6132721634264133/100000000000000 : ℝ)*(sp0) + (3066379876143977/50000000000000 : ℝ)*(sp1) + (6132759874128997/100000000000000 : ℝ)*(sp2) + (356706584694347/12500000000000 : ℝ)*(sp3) + (5007944981/12500000000000 : ℝ)*(sp4) + (21748653971/100000000000000 : ℝ)*(sp7) + (2853674426208747/100000000000000 : ℝ)*(f.failure) + (6132761697823981/100000000000000 : ℝ)*(f.sum) + (264320829213/87700000000000000000000000 : ℝ)*base66 + (96717090661723863/10962500000000000000000000000000 : ℝ)*base68 + (3709912738924611/685156250000000000000000000000 : ℝ)*base69 + (39140325140098863/10962500000000000000000000000000 : ℝ)*base72 + (1268947685329/219250000000000000000000000 : ℝ)*base74 + (3531999512632819/2740625000000000000000000000000 : ℝ)*base75 + (161430772256348863/10962500000000000000000000000000 : ℝ)*base78 + (98324337279698863/10962500000000000000000000000000 : ℝ)*base80 + (317696728179/438500000000000000000000000 : ℝ)*base82 + (789317/500000000000000000000 : ℝ)*base90 + (789317/500000000000000000000 : ℝ)*base92 + (5789317/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6232371945018834010431/877000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1214616287/100000000000000 : ℝ)*(base19) + (65681057/5000000000000 : ℝ)*(base23) + (292043/200000000000 : ℝ)*(upper3) + (45831909/100000000000000 : ℝ)*(lower4) + (5846593/4000000000000 : ℝ)*(upper5) + (226295775691473/5000000000000 : ℝ)*(major0) + (226295775691473/5000000000000 : ℝ)*(major1) + (226295775691473/5000000000000 : ℝ)*(major2) + (25336336783/100000000000000 : ℝ)*(sp1) + (27210343833/100000000000000 : ℝ)*(sp2) + (3088695052431351/50000000000000 : ℝ)*(sp4) + (6177363553909633/100000000000000 : ℝ)*(sp5) + (6177361580897729/100000000000000 : ℝ)*(sp6) + (2874440685913961/100000000000000 : ℝ)*(sp7) + (2874440685913961/100000000000000 : ℝ)*(f.failure) + (3088695052431351/50000000000000 : ℝ)*(f.sum) + (116661610811/109625000000000000000000000 : ℝ)*base65 + (3360827529515997/548125000000000000000000000000 : ℝ)*base67 + (2036205017592061/274062500000000000000000000000 : ℝ)*base69 + (1328178199087939/274062500000000000000000000000 : ℝ)*base72 + (800118029141/438500000000000000000000000 : ℝ)*base73 + (1068161608098657/137031250000000000000000000000 : ℝ)*base76 + (1349209416437247/548125000000000000000000000000 : ℝ)*base77 + (1175903154337939/274062500000000000000000000000 : ℝ)*base80 + (1065584589139/877000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (4288871/500000000000000000000 : ℝ)*base90 + (4288871/500000000000000000000 : ℝ)*base92 + (4288871/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1411_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (739/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1409/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1411_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1411_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (991/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1411_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1411_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1411_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2185/512 : ℝ) ≤ p) (hpb : p ≤ (4371/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7872689/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (991/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5649/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1411_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
