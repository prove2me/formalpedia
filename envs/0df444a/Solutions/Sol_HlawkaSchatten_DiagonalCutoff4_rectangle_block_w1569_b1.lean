-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1569_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:27:11.09831+00:00
-- url     : https://prove2.me/submissions/5f381cfd-788f-4b88-813c-d87ec5ac3cc9

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
theorem support_rectangle_w1569_s3_0 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1786729681/10000000000 : ℝ)*x 0 + (2713803869/5000000000 : ℝ)*x 1 + (163078269/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1786729681/10000000000 : ℝ)^4635 ≤ (1370469083711/12500000000000 : ℝ)^3611 := by
    have hnat : (1786729681 : ℕ)^4635*12500000000000^3611 ≤ 1370469083711^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786729681 10000000000 1370469083711 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713803869/5000000000 : ℝ)^4635 ≤ (45640380920723/100000000000000 : ℝ)^3611 := by
    have hnat : (2713803869 : ℕ)^4635*100000000000000^3611 ≤ 45640380920723^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713803869 5000000000 45640380920723 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163078269/312500000 : ℝ)^4635 ≤ (21697933197947/50000000000000 : ℝ)^3611 := by
    have hnat : (163078269 : ℕ)^4635*50000000000000^3611 ≤ 21697933197947^3611*312500000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163078269 312500000 21697933197947 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1786729681/10000000000 : ℝ), (2713803869/5000000000 : ℝ), (163078269/312500000 : ℝ)] ![(1370469083711/12500000000000 : ℝ), (45640380920723/100000000000000 : ℝ), (21697933197947/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1786729681/10000000000 : ℝ)|^4635 ≤ (1370469083711/12500000000000 : ℝ)^3611
        have hw : |(-1786729681/10000000000 : ℝ)|=(1786729681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713803869/5000000000 : ℝ)|^4635 ≤ (45640380920723/100000000000000 : ℝ)^3611
        have hw : |(2713803869/5000000000 : ℝ)|=(2713803869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163078269/312500000 : ℝ)|^4635 ≤ (21697933197947/50000000000000 : ℝ)^3611
        have hw : |(163078269/312500000 : ℝ)|=(163078269/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s3_1 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674349931/5000000000 : ℝ)*x 0 + (-946871741/5000000000 : ℝ)*x 1 + (652313079/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674349931/5000000000 : ℝ)^4635 ≤ (44790449050421/100000000000000 : ℝ)^3611 := by
    have hnat : (2674349931 : ℕ)^4635*100000000000000^3611 ≤ 44790449050421^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674349931 5000000000 44790449050421 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946871741/5000000000 : ℝ)^4635 ≤ (2953421069209/25000000000000 : ℝ)^3611 := by
    have hnat : (946871741 : ℕ)^4635*25000000000000^3611 ≤ 2953421069209^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946871741 5000000000 2953421069209 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652313079/1250000000 : ℝ)^4635 ≤ (10848966663017/25000000000000 : ℝ)^3611 := by
    have hnat : (652313079 : ℕ)^4635*25000000000000^3611 ≤ 10848966663017^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652313079 1250000000 10848966663017 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674349931/5000000000 : ℝ), (-946871741/5000000000 : ℝ), (652313079/1250000000 : ℝ)] ![(44790449050421/100000000000000 : ℝ), (2953421069209/25000000000000 : ℝ), (10848966663017/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674349931/5000000000 : ℝ)|^4635 ≤ (44790449050421/100000000000000 : ℝ)^3611
        have hw : |(2674349931/5000000000 : ℝ)|=(2674349931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-946871741/5000000000 : ℝ)|^4635 ≤ (2953421069209/25000000000000 : ℝ)^3611
        have hw : |(-946871741/5000000000 : ℝ)|=(946871741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652313079/1250000000 : ℝ)|^4635 ≤ (10848966663017/25000000000000 : ℝ)^3611
        have hw : |(652313079/1250000000 : ℝ)|=(652313079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s3_2 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348699857/10000000000 : ℝ)*x 0 + (2609252311/5000000000 : ℝ)*x 1 + (-118358969/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348699857/10000000000 : ℝ)^4635 ≤ (44790448996677/100000000000000 : ℝ)^3611 := by
    have hnat : (5348699857 : ℕ)^4635*100000000000000^3611 ≤ 44790448996677^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348699857 10000000000 44790448996677 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609252311/5000000000 : ℝ)^4635 ≤ (43395866545329/100000000000000 : ℝ)^3611 := by
    have hnat : (2609252311 : ℕ)^4635*100000000000000^3611 ≤ 43395866545329^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609252311 5000000000 43395866545329 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (118358969/625000000 : ℝ)^4635 ≤ (11813684452997/100000000000000 : ℝ)^3611 := by
    have hnat : (118358969 : ℕ)^4635*100000000000000^3611 ≤ 11813684452997^3611*625000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118358969 625000000 11813684452997 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348699857/10000000000 : ℝ), (2609252311/5000000000 : ℝ), (-118358969/625000000 : ℝ)] ![(44790448996677/100000000000000 : ℝ), (43395866545329/100000000000000 : ℝ), (11813684452997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348699857/10000000000 : ℝ)|^4635 ≤ (44790448996677/100000000000000 : ℝ)^3611
        have hw : |(5348699857/10000000000 : ℝ)|=(5348699857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609252311/5000000000 : ℝ)|^4635 ≤ (43395866545329/100000000000000 : ℝ)^3611
        have hw : |(2609252311/5000000000 : ℝ)|=(2609252311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-118358969/625000000 : ℝ)|^4635 ≤ (11813684452997/100000000000000 : ℝ)^3611
        have hw : |(-118358969/625000000 : ℝ)|=(118358969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s3_3 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530473361/1250000000 : ℝ)*x 0 + (1000740731/2500000000 : ℝ)*x 1 + (899245517/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530473361/1250000000 : ℝ)^4635 ≤ (33280717741373/100000000000000 : ℝ)^3611 := by
    have hnat : (530473361 : ℕ)^4635*100000000000000^3611 ≤ 33280717741373^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530473361 1250000000 33280717741373 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1000740731/2500000000 : ℝ)^4635 ≤ (30876335067367/100000000000000 : ℝ)^3611 := by
    have hnat : (1000740731 : ℕ)^4635*100000000000000^3611 ≤ 30876335067367^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000740731 2500000000 30876335067367 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899245517/2000000000 : ℝ)^4635 ≤ (35842947169109/100000000000000 : ℝ)^3611 := by
    have hnat : (899245517 : ℕ)^4635*100000000000000^3611 ≤ 35842947169109^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899245517 2000000000 35842947169109 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530473361/1250000000 : ℝ), (1000740731/2500000000 : ℝ), (899245517/2000000000 : ℝ)] ![(33280717741373/100000000000000 : ℝ), (30876335067367/100000000000000 : ℝ), (35842947169109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530473361/1250000000 : ℝ)|^4635 ≤ (33280717741373/100000000000000 : ℝ)^3611
        have hw : |(530473361/1250000000 : ℝ)|=(530473361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1000740731/2500000000 : ℝ)|^4635 ≤ (30876335067367/100000000000000 : ℝ)^3611
        have hw : |(1000740731/2500000000 : ℝ)|=(1000740731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899245517/2000000000 : ℝ)|^4635 ≤ (35842947169109/100000000000000 : ℝ)^3611
        have hw : |(899245517/2000000000 : ℝ)|=(899245517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s3_4 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-893378723/5000000000 : ℝ)*x 0 + (5219610533/10000000000 : ℝ)*x 1 + (5426493739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (893378723/5000000000 : ℝ)^4635 ≤ (1096397135583/10000000000000 : ℝ)^3611 := by
    have hnat : (893378723 : ℕ)^4635*10000000000000^3611 ≤ 1096397135583^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893378723 5000000000 1096397135583 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219610533/10000000000 : ℝ)^4635 ≤ (8681534264367/20000000000000 : ℝ)^3611 := by
    have hnat : (5219610533 : ℕ)^4635*20000000000000^3611 ≤ 8681534264367^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219610533 10000000000 8681534264367 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426493739/10000000000 : ℝ)^4635 ≤ (11407089325341/25000000000000 : ℝ)^3611 := by
    have hnat : (5426493739 : ℕ)^4635*25000000000000^3611 ≤ 11407089325341^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426493739 10000000000 11407089325341 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-893378723/5000000000 : ℝ), (5219610533/10000000000 : ℝ), (5426493739/10000000000 : ℝ)] ![(1096397135583/10000000000000 : ℝ), (8681534264367/20000000000000 : ℝ), (11407089325341/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-893378723/5000000000 : ℝ)|^4635 ≤ (1096397135583/10000000000000 : ℝ)^3611
        have hw : |(-893378723/5000000000 : ℝ)|=(893378723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219610533/10000000000 : ℝ)|^4635 ≤ (8681534264367/20000000000000 : ℝ)^3611
        have hw : |(5219610533/10000000000 : ℝ)|=(5219610533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426493739/10000000000 : ℝ)|^4635 ≤ (11407089325341/25000000000000 : ℝ)^3611
        have hw : |(5426493739/10000000000 : ℝ)|=(5426493739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s3_5 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293383853/10000000000 : ℝ)*x 0 + (-421438709/2500000000 : ℝ)*x 1 + (1085298651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293383853/10000000000 : ℝ)^4635 ≤ (44196743117957/100000000000000 : ℝ)^3611 := by
    have hnat : (5293383853 : ℕ)^4635*100000000000000^3611 ≤ 44196743117957^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293383853 10000000000 44196743117957 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421438709/2500000000 : ℝ)^4635 ≤ (635931549937/6250000000000 : ℝ)^3611 := by
    have hnat : (421438709 : ℕ)^4635*6250000000000^3611 ≤ 635931549937^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421438709 2500000000 635931549937 6250000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085298651/2000000000 : ℝ)^4635 ≤ (9125670415521/20000000000000 : ℝ)^3611 := by
    have hnat : (1085298651 : ℕ)^4635*20000000000000^3611 ≤ 9125670415521^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085298651 2000000000 9125670415521 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293383853/10000000000 : ℝ), (-421438709/2500000000 : ℝ), (1085298651/2000000000 : ℝ)] ![(44196743117957/100000000000000 : ℝ), (635931549937/6250000000000 : ℝ), (9125670415521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293383853/10000000000 : ℝ)|^4635 ≤ (44196743117957/100000000000000 : ℝ)^3611
        have hw : |(5293383853/10000000000 : ℝ)|=(5293383853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421438709/2500000000 : ℝ)|^4635 ≤ (635931549937/6250000000000 : ℝ)^3611
        have hw : |(-421438709/2500000000 : ℝ)|=(421438709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085298651/2000000000 : ℝ)|^4635 ≤ (9125670415521/20000000000000 : ℝ)^3611
        have hw : |(1085298651/2000000000 : ℝ)|=(1085298651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s3_6 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661673033/1250000000 : ℝ)*x 0 + (678311649/1250000000 : ℝ)*x 1 + (-842877177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661673033/1250000000 : ℝ)^4635 ≤ (44196747522703/100000000000000 : ℝ)^3611 := by
    have hnat : (661673033 : ℕ)^4635*100000000000000^3611 ≤ 44196747522703^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661673033 1250000000 44196747522703 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678311649/1250000000 : ℝ)^4635 ≤ (45628351397653/100000000000000 : ℝ)^3611 := by
    have hnat : (678311649 : ℕ)^4635*100000000000000^3611 ≤ 45628351397653^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678311649 1250000000 45628351397653 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (842877177/5000000000 : ℝ)^4635 ≤ (5087450532363/50000000000000 : ℝ)^3611 := by
    have hnat : (842877177 : ℕ)^4635*50000000000000^3611 ≤ 5087450532363^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842877177 5000000000 5087450532363 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661673033/1250000000 : ℝ), (678311649/1250000000 : ℝ), (-842877177/5000000000 : ℝ)] ![(44196747522703/100000000000000 : ℝ), (45628351397653/100000000000000 : ℝ), (5087450532363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661673033/1250000000 : ℝ)|^4635 ≤ (44196747522703/100000000000000 : ℝ)^3611
        have hw : |(661673033/1250000000 : ℝ)|=(661673033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678311649/1250000000 : ℝ)|^4635 ≤ (45628351397653/100000000000000 : ℝ)^3611
        have hw : |(678311649/1250000000 : ℝ)|=(678311649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-842877177/5000000000 : ℝ)|^4635 ≤ (5087450532363/50000000000000 : ℝ)^3611
        have hw : |(-842877177/5000000000 : ℝ)|=(842877177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s3_7 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121926679/5000000000 : ℝ)*x 0 + (2246809681/5000000000 : ℝ)*x 1 + (4005590481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121926679/5000000000 : ℝ)^4635 ≤ (33281386836721/100000000000000 : ℝ)^3611 := by
    have hnat : (2121926679 : ℕ)^4635*100000000000000^3611 ≤ 33281386836721^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121926679 5000000000 33281386836721 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2246809681/5000000000 : ℝ)^4635 ≤ (35816260973237/100000000000000 : ℝ)^3611 := by
    have hnat : (2246809681 : ℕ)^4635*100000000000000^3611 ≤ 35816260973237^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246809681 5000000000 35816260973237 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4005590481/10000000000 : ℝ)^4635 ≤ (30902352173317/100000000000000 : ℝ)^3611 := by
    have hnat : (4005590481 : ℕ)^4635*100000000000000^3611 ≤ 30902352173317^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4005590481 10000000000 30902352173317 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121926679/5000000000 : ℝ), (2246809681/5000000000 : ℝ), (4005590481/10000000000 : ℝ)] ![(33281386836721/100000000000000 : ℝ), (35816260973237/100000000000000 : ℝ), (30902352173317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121926679/5000000000 : ℝ)|^4635 ≤ (33281386836721/100000000000000 : ℝ)^3611
        have hw : |(2121926679/5000000000 : ℝ)|=(2121926679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2246809681/5000000000 : ℝ)|^4635 ≤ (35816260973237/100000000000000 : ℝ)^3611
        have hw : |(2246809681/5000000000 : ℝ)|=(2246809681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4005590481/10000000000 : ℝ)|^4635 ≤ (30902352173317/100000000000000 : ℝ)^3611
        have hw : |(4005590481/10000000000 : ℝ)|=(4005590481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1569_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7907/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2217/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (97/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7907/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7907/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5407/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7907/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7907/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5407/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7907/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7907/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5407/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5407/50000 : ℝ) ^ (4633/1024 : ℝ) ≤ (4259457863116003/100000000000000000000 : ℝ) := by
    have hpowers : (5407/50000 : ℝ)^4633 ≤ (4259457863116003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5407 : ℕ)^4633*100000000000000000000^1024 ≤ 4259457863116003^1024*50000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5407 50000 4259457863116003 100000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5407/50000 : ℝ)) (X := (4259457863116003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7907/50000 : ℝ) ^ (4633/1024 : ℝ) ≤ (1188784583118237/5000000000000000000 : ℝ) := by
    have hpowers : (7907/50000 : ℝ)^4633 ≤ (1188784583118237/5000000000000000000 : ℝ)^1024 := by
      have hnat : (7907 : ℕ)^4633*5000000000000000000^1024 ≤ 1188784583118237^1024*50000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7907 50000 1188784583118237 5000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7907/50000 : ℝ)) (X := (1188784583118237/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004259457863116003/50000000000000000000 : ℝ) ≤ (5000094140732519/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50004259457863116003/50000000000000000000 : ℝ)^1024 ≤ (5000094140732519/5000000000000000 : ℝ)^4633 := by
      have hnat : (50004259457863116003 : ℕ)^1024*5000000000000000^4633 ≤ 5000094140732519^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004259457863116003 50000000000000000000 5000094140732519 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000094140732519/5000000000000000 : ℝ)) (X := (50004259457863116003/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028035149525480743/100000000000000000000 : ℝ) ≤ (5000309786951263/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (100028035149525480743/100000000000000000000 : ℝ)^1024 ≤ (5000309786951263/5000000000000000 : ℝ)^4633 := by
      have hnat : (100028035149525480743 : ℕ)^1024*5000000000000000^4633 ≤ 5000309786951263^4633*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028035149525480743 100000000000000000000 5000309786951263 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000309786951263/5000000000000000 : ℝ)) (X := (100028035149525480743/100000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501188784583118237/2500000000000000000 : ℝ) ≤ (5000525433170007/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (2501188784583118237/2500000000000000000 : ℝ)^1024 ≤ (5000525433170007/5000000000000000 : ℝ)^4633 := by
      have hnat : (2501188784583118237 : ℕ)^1024*5000000000000000^4633 ≤ 5000525433170007^4633*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501188784583118237 2500000000000000000 5000525433170007 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000525433170007/5000000000000000 : ℝ)) (X := (2501188784583118237/2500000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4259457863116003/100000000000000000000 : ℝ) ≤ ((3124475838405449971/3125000000000000000 : ℝ)+2*(26955777343/31250000000000 : ℝ)*(5407/50000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (3124475838405449971/3125000000000000000 : ℝ)+2*(26955777343/31250000000000 : ℝ)*(5407/50000 : ℝ)=(5000094140732519/5000000000000000 : ℝ) by norm_num, show 1+2*(4259457863116003/100000000000000000000 : ℝ)=(50004259457863116003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1188784583118237/5000000000000000000 : ℝ)+(4259457863116003/100000000000000000000 : ℝ) ≤ ((3124475838405449971/3125000000000000000 : ℝ)+(26955777343/31250000000000 : ℝ)*((7907/50000 : ℝ)+(5407/50000 : ℝ)))^(4633/1024 : ℝ) := by
    rw [show (3124475838405449971/3125000000000000000 : ℝ)+(26955777343/31250000000000 : ℝ)*((7907/50000 : ℝ)+(5407/50000 : ℝ))=(5000309786951263/5000000000000000 : ℝ) by norm_num, show 1+(1188784583118237/5000000000000000000 : ℝ)+(4259457863116003/100000000000000000000 : ℝ)=(100028035149525480743/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1188784583118237/5000000000000000000 : ℝ) ≤ ((3124475838405449971/3125000000000000000 : ℝ)+2*(26955777343/31250000000000 : ℝ)*(7907/50000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (3124475838405449971/3125000000000000000 : ℝ)+2*(26955777343/31250000000000 : ℝ)*(7907/50000 : ℝ)=(5000525433170007/5000000000000000 : ℝ) by norm_num, show 1+2*(1188784583118237/5000000000000000000 : ℝ)=(2501188784583118237/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3124475838405449971/3125000000000000000 : ℝ)*(X 1 0+X 2 0)+(26955777343/31250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (7907/50000 : ℝ)) (c := (3124475838405449971/3125000000000000000 : ℝ)) (alpha := (26955777343/31250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3124475838405449971/3125000000000000000 : ℝ)*(X 0 1+X 2 1)+(26955777343/31250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (7907/50000 : ℝ)) (c := (3124475838405449971/3125000000000000000 : ℝ)) (alpha := (26955777343/31250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3124475838405449971/3125000000000000000 : ℝ)*(X 0 2+X 1 2)+(26955777343/31250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (5407/50000 : ℝ)) (hi := (7907/50000 : ℝ)) (c := (3124475838405449971/3125000000000000000 : ℝ)) (alpha := (26955777343/31250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1786729681/10000000000 : ℝ)*X 0 0+(2713803869/5000000000 : ℝ)*X 0 1+(163078269/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674349931/5000000000 : ℝ)*X 1 0+(-946871741/5000000000 : ℝ)*X 1 1+(652313079/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348699857/10000000000 : ℝ)*X 2 0+(2609252311/5000000000 : ℝ)*X 2 1+(-118358969/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((530473361/1250000000 : ℝ)*X 0 0+(1000740731/2500000000 : ℝ)*X 0 1+(899245517/2000000000 : ℝ)*X 0 2+(530473361/1250000000 : ℝ)*X 1 0+(1000740731/2500000000 : ℝ)*X 1 1+(899245517/2000000000 : ℝ)*X 1 2+(530473361/1250000000 : ℝ)*X 2 0+(1000740731/2500000000 : ℝ)*X 2 1+(899245517/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-893378723/5000000000 : ℝ)*X 0 0+(5219610533/10000000000 : ℝ)*X 0 1+(5426493739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293383853/10000000000 : ℝ)*X 1 0+(-421438709/2500000000 : ℝ)*X 1 1+(1085298651/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661673033/1250000000 : ℝ)*X 2 0+(678311649/1250000000 : ℝ)*X 2 1+(-842877177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121926679/5000000000 : ℝ)*X 0 0+(2246809681/5000000000 : ℝ)*X 0 1+(4005590481/10000000000 : ℝ)*X 0 2+(2121926679/5000000000 : ℝ)*X 1 0+(2246809681/5000000000 : ℝ)*X 1 1+(4005590481/10000000000 : ℝ)*X 1 2+(2121926679/5000000000 : ℝ)*X 2 0+(2246809681/5000000000 : ℝ)*X 2 1+(4005590481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (927837511449248008121526681/78125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1984301621/100000000000000 : ℝ)*(base19) + (1860141689/100000000000000 : ℝ)*(base23) + (4001139/6250000000000 : ℝ)*(lower2) + (150134417/50000000000000 : ℝ)*(upper3) + (47966371/25000000000000 : ℝ)*(upper5) + (1702432969062663/50000000000000 : ℝ)*(major0) + (1702432969062663/50000000000000 : ℝ)*(major1) + (1702432969062663/50000000000000 : ℝ)*(major2) + (597795336363331/12500000000000 : ℝ)*(sp0) + (18681220465311/390625000000 : ℝ)*(sp1) + (1195598140819887/25000000000000 : ℝ)*(sp2) + (405464462257787/20000000000000 : ℝ)*(sp3) + (31732514589/100000000000000 : ℝ)*(sp4) + (7372831569/50000000000000 : ℝ)*(sp7) + (2027337056952073/100000000000000 : ℝ)*(f.failure) + (4782394423421237/100000000000000 : ℝ)*(f.sum) + (6849706433057/1562500000000000000000000000 : ℝ)*base66 + (728305124854817227/156250000000000000000000000000000 : ℝ)*base68 + (460660257801432773/156250000000000000000000000000000 : ℝ)*base69 + (383981965926432773/156250000000000000000000000000000 : ℝ)*base71 + (2952336249341/781250000000000000000000000 : ℝ)*base74 + (167290092645182773/156250000000000000000000000000000 : ℝ)*base75 + (918819853448567227/156250000000000000000000000000000 : ℝ)*base78 + (1384966329051432773/156250000000000000000000000000000 : ℝ)*base79 + (7528079449511/3125000000000000000000000000 : ℝ)*base81 + (13630027/10000000000000000000000 : ℝ)*base89 + (13630027/10000000000000000000000 : ℝ)*base91 + (13630027/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (631977445174439154186256671/78125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (207858891/20000000000000 : ℝ)*(base19) + (1056783519/50000000000000 : ℝ)*(base23) + (12019261/6250000000000 : ℝ)*(upper3) + (24088777/10000000000000 : ℝ)*(lower4) + (23710843/50000000000000 : ℝ)*(upper5) + (1720675036129189/50000000000000 : ℝ)*(major0) + (1720675036129189/50000000000000 : ℝ)*(major1) + (1720675036129189/50000000000000 : ℝ)*(major2) + (2359056951/100000000000000 : ℝ)*(sp1) + (12849253727/50000000000000 : ℝ)*(sp2) + (2416819654274267/50000000000000 : ℝ)*(sp4) + (604204488774641/12500000000000 : ℝ)*(sp5) + (2416805748237021/50000000000000 : ℝ)*(sp6) + (2049060566324507/100000000000000 : ℝ)*(sp7) + (2049060566324507/100000000000000 : ℝ)*(f.failure) + (2416819654274267/50000000000000 : ℝ)*(f.sum) + (5221403704721/1562500000000000000000000000 : ℝ)*base66 + (669540953509996481/156250000000000000000000000000000 : ℝ)*base68 + (396171162416246481/156250000000000000000000000000000 : ℝ)*base70 + (529485687259996481/156250000000000000000000000000000 : ℝ)*base72 + (1669443885173/781250000000000000000000000 : ℝ)*base74 + (1619458669603746481/156250000000000000000000000000000 : ℝ)*base76 + (1477062909134996481/156250000000000000000000000000000 : ℝ)*base78 + (1155488739447496481/156250000000000000000000000000000 : ℝ)*base80 + (12163755587433/3125000000000000000000000000 : ℝ)*base81 + (37959393/10000000000000000000000 : ℝ)*base89 + (37959393/10000000000000000000000 : ℝ)*base91 + (37959393/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1569_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7907/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (97/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1569_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1569_s4_0 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1786957167/10000000000 : ℝ)*x 0 + (169565097/312500000 : ℝ)*x 1 + (1043975669/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1786957167/10000000000 : ℝ)^4635 ≤ (438621778063/4000000000000 : ℝ)^3611 := by
    have hnat : (1786957167 : ℕ)^4635*4000000000000^3611 ≤ 438621778063^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786957167 10000000000 438621778063 4000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169565097/312500000 : ℝ)^4635 ≤ (2281196270513/5000000000000 : ℝ)^3611 := by
    have hnat : (169565097 : ℕ)^4635*5000000000000^3611 ≤ 2281196270513^3611*312500000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169565097 312500000 2281196270513 5000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043975669/2000000000 : ℝ)^4635 ≤ (43410530122217/100000000000000 : ℝ)^3611 := by
    have hnat : (1043975669 : ℕ)^4635*100000000000000^3611 ≤ 43410530122217^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043975669 2000000000 43410530122217 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1786957167/10000000000 : ℝ), (169565097/312500000 : ℝ), (1043975669/2000000000 : ℝ)] ![(438621778063/4000000000000 : ℝ), (2281196270513/5000000000000 : ℝ), (43410530122217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1786957167/10000000000 : ℝ)|^4635 ≤ (438621778063/4000000000000 : ℝ)^3611
        have hw : |(-1786957167/10000000000 : ℝ)|=(1786957167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169565097/312500000 : ℝ)|^4635 ≤ (2281196270513/5000000000000 : ℝ)^3611
        have hw : |(169565097/312500000 : ℝ)|=(169565097/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043975669/2000000000 : ℝ)|^4635 ≤ (43410530122217/100000000000000 : ℝ)^3611
        have hw : |(1043975669/2000000000 : ℝ)|=(1043975669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s4_1 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337074027/2500000000 : ℝ)*x 0 + (-473113523/2500000000 : ℝ)*x 1 + (1043975667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337074027/2500000000 : ℝ)^4635 ≤ (22393054615657/50000000000000 : ℝ)^3611 := by
    have hnat : (1337074027 : ℕ)^4635*50000000000000^3611 ≤ 22393054615657^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337074027 2500000000 22393054615657 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473113523/2500000000 : ℝ)^4635 ≤ (11803360732643/100000000000000 : ℝ)^3611 := by
    have hnat : (473113523 : ℕ)^4635*100000000000000^3611 ≤ 11803360732643^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473113523 2500000000 11803360732643 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043975667/2000000000 : ℝ)^4635 ≤ (4341053001547/10000000000000 : ℝ)^3611 := by
    have hnat : (1043975667 : ℕ)^4635*10000000000000^3611 ≤ 4341053001547^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043975667 2000000000 4341053001547 10000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337074027/2500000000 : ℝ), (-473113523/2500000000 : ℝ), (1043975667/2000000000 : ℝ)] ![(22393054615657/50000000000000 : ℝ), (11803360732643/100000000000000 : ℝ), (4341053001547/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337074027/2500000000 : ℝ)|^4635 ≤ (22393054615657/50000000000000 : ℝ)^3611
        have hw : |(1337074027/2500000000 : ℝ)|=(1337074027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473113523/2500000000 : ℝ)|^4635 ≤ (11803360732643/100000000000000 : ℝ)^3611
        have hw : |(-473113523/2500000000 : ℝ)|=(473113523/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043975667/2000000000 : ℝ)|^4635 ≤ (4341053001547/10000000000000 : ℝ)^3611
        have hw : |(1043975667/2000000000 : ℝ)|=(1043975667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s4_2 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674148053/5000000000 : ℝ)*x 0 + (5219878351/10000000000 : ℝ)*x 1 + (-946227037/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674148053/5000000000 : ℝ)^4635 ≤ (44786109209817/100000000000000 : ℝ)^3611 := by
    have hnat : (2674148053 : ℕ)^4635*100000000000000^3611 ≤ 44786109209817^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674148053 5000000000 44786109209817 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219878351/10000000000 : ℝ)^4635 ≤ (8682106037253/20000000000000 : ℝ)^3611 := by
    have hnat : (5219878351 : ℕ)^4635*20000000000000^3611 ≤ 8682106037253^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219878351 10000000000 8682106037253 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946227037/5000000000 : ℝ)^4635 ≤ (11803360588539/100000000000000 : ℝ)^3611 := by
    have hnat : (946227037 : ℕ)^4635*100000000000000^3611 ≤ 11803360588539^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946227037 5000000000 11803360588539 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674148053/5000000000 : ℝ), (5219878351/10000000000 : ℝ), (-946227037/5000000000 : ℝ)] ![(44786109209817/100000000000000 : ℝ), (8682106037253/20000000000000 : ℝ), (11803360588539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674148053/5000000000 : ℝ)|^4635 ≤ (44786109209817/100000000000000 : ℝ)^3611
        have hw : |(2674148053/5000000000 : ℝ)|=(2674148053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219878351/10000000000 : ℝ)|^4635 ≤ (8682106037253/20000000000000 : ℝ)^3611
        have hw : |(5219878351/10000000000 : ℝ)|=(5219878351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-946227037/5000000000 : ℝ)|^4635 ≤ (11803360588539/100000000000000 : ℝ)^3611
        have hw : |(-946227037/5000000000 : ℝ)|=(946227037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s4_3 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060982669/2500000000 : ℝ)*x 0 + (2003182777/5000000000 : ℝ)*x 1 + (2246396517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060982669/2500000000 : ℝ)^4635 ≤ (6656433026627/20000000000000 : ℝ)^3611 := by
    have hnat : (1060982669 : ℕ)^4635*20000000000000^3611 ≤ 6656433026627^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060982669 2500000000 6656433026627 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003182777/5000000000 : ℝ)^4635 ≤ (30910027586507/100000000000000 : ℝ)^3611 := by
    have hnat : (2003182777 : ℕ)^4635*100000000000000^3611 ≤ 30910027586507^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003182777 5000000000 30910027586507 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246396517/5000000000 : ℝ)^4635 ≤ (35807807262983/100000000000000 : ℝ)^3611 := by
    have hnat : (2246396517 : ℕ)^4635*100000000000000^3611 ≤ 35807807262983^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246396517 5000000000 35807807262983 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060982669/2500000000 : ℝ), (2003182777/5000000000 : ℝ), (2246396517/5000000000 : ℝ)] ![(6656433026627/20000000000000 : ℝ), (30910027586507/100000000000000 : ℝ), (35807807262983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060982669/2500000000 : ℝ)|^4635 ≤ (6656433026627/20000000000000 : ℝ)^3611
        have hw : |(1060982669/2500000000 : ℝ)|=(1060982669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2003182777/5000000000 : ℝ)|^4635 ≤ (30910027586507/100000000000000 : ℝ)^3611
        have hw : |(2003182777/5000000000 : ℝ)|=(2003182777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246396517/5000000000 : ℝ)|^4635 ≤ (35807807262983/100000000000000 : ℝ)^3611
        have hw : |(2246396517/5000000000 : ℝ)|=(2246396517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s4_4 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1786984109/10000000000 : ℝ)*x 0 + (652619229/1250000000 : ℝ)*x 1 + (1356249911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1786984109/10000000000 : ℝ)^4635 ≤ (10965756663149/100000000000000 : ℝ)^3611 := by
    have hnat : (1786984109 : ℕ)^4635*100000000000000^3611 ≤ 10965756663149^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786984109 10000000000 10965756663149 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652619229/1250000000 : ℝ)^4635 ≤ (43422010992493/100000000000000 : ℝ)^3611 := by
    have hnat : (652619229 : ℕ)^4635*100000000000000^3611 ≤ 43422010992493^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652619229 1250000000 43422010992493 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356249911/2500000000 : ℝ)^4635 ≤ (45612232326961/100000000000000 : ℝ)^3611 := by
    have hnat : (1356249911 : ℕ)^4635*100000000000000^3611 ≤ 45612232326961^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356249911 2500000000 45612232326961 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1786984109/10000000000 : ℝ), (652619229/1250000000 : ℝ), (1356249911/2500000000 : ℝ)] ![(10965756663149/100000000000000 : ℝ), (43422010992493/100000000000000 : ℝ), (45612232326961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1786984109/10000000000 : ℝ)|^4635 ≤ (10965756663149/100000000000000 : ℝ)^3611
        have hw : |(-1786984109/10000000000 : ℝ)|=(1786984109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652619229/1250000000 : ℝ)|^4635 ≤ (43422010992493/100000000000000 : ℝ)^3611
        have hw : |(652619229/1250000000 : ℝ)|=(652619229/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356249911/2500000000 : ℝ)|^4635 ≤ (45612232326961/100000000000000 : ℝ)^3611
        have hw : |(1356249911/2500000000 : ℝ)|=(1356249911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s4_5 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293747097/10000000000 : ℝ)*x 0 + (-1687332793/10000000000 : ℝ)*x 1 + (2712499823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293747097/10000000000 : ℝ)^4635 ≤ (11050159023663/25000000000000 : ℝ)^3611 := by
    have hnat : (5293747097 : ℕ)^4635*25000000000000^3611 ≤ 11050159023663^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293747097 10000000000 11050159023663 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1687332793/10000000000 : ℝ)^4635 ≤ (5093565773737/50000000000000 : ℝ)^3611 := by
    have hnat : (1687332793 : ℕ)^4635*50000000000000^3611 ≤ 5093565773737^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687332793 10000000000 5093565773737 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712499823/5000000000 : ℝ)^4635 ≤ (9122446469709/20000000000000 : ℝ)^3611 := by
    have hnat : (2712499823 : ℕ)^4635*20000000000000^3611 ≤ 9122446469709^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712499823 5000000000 9122446469709 20000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293747097/10000000000 : ℝ), (-1687332793/10000000000 : ℝ), (2712499823/5000000000 : ℝ)] ![(11050159023663/25000000000000 : ℝ), (5093565773737/50000000000000 : ℝ), (9122446469709/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293747097/10000000000 : ℝ)|^4635 ≤ (11050159023663/25000000000000 : ℝ)^3611
        have hw : |(5293747097/10000000000 : ℝ)|=(5293747097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1687332793/10000000000 : ℝ)|^4635 ≤ (5093565773737/50000000000000 : ℝ)^3611
        have hw : |(-1687332793/10000000000 : ℝ)|=(1687332793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712499823/5000000000 : ℝ)|^4635 ≤ (9122446469709/20000000000000 : ℝ)^3611
        have hw : |(2712499823/5000000000 : ℝ)|=(2712499823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s4_6 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165429597/312500000 : ℝ)*x 0 + (2712499821/5000000000 : ℝ)*x 1 + (-1687332789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165429597/312500000 : ℝ)^4635 ≤ (44200636169673/100000000000000 : ℝ)^3611 := by
    have hnat : (165429597 : ℕ)^4635*100000000000000^3611 ≤ 44200636169673^3611*312500000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165429597 312500000 44200636169673 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712499821/5000000000 : ℝ)^4635 ≤ (45612232305377/100000000000000 : ℝ)^3611 := by
    have hnat : (2712499821 : ℕ)^4635*100000000000000^3611 ≤ 45612232305377^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712499821 5000000000 45612232305377 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1687332789/10000000000 : ℝ)^4635 ≤ (2546782879119/25000000000000 : ℝ)^3611 := by
    have hnat : (1687332789 : ℕ)^4635*25000000000000^3611 ≤ 2546782879119^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687332789 10000000000 2546782879119 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165429597/312500000 : ℝ), (2712499821/5000000000 : ℝ), (-1687332789/10000000000 : ℝ)] ![(44200636169673/100000000000000 : ℝ), (45612232305377/100000000000000 : ℝ), (2546782879119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165429597/312500000 : ℝ)|^4635 ≤ (44200636169673/100000000000000 : ℝ)^3611
        have hw : |(165429597/312500000 : ℝ)|=(165429597/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712499821/5000000000 : ℝ)|^4635 ≤ (45612232305377/100000000000000 : ℝ)^3611
        have hw : |(2712499821/5000000000 : ℝ)|=(2712499821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1687332789/10000000000 : ℝ)|^4635 ≤ (2546782879119/25000000000000 : ℝ)^3611
        have hw : |(-1687332789/10000000000 : ℝ)|=(1687332789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s4_7 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121997101/5000000000 : ℝ)*x 0 + (1122563999/2500000000 : ℝ)*x 1 + (32071371/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121997101/5000000000 : ℝ)^4635 ≤ (8320701149973/25000000000000 : ℝ)^3611 := by
    have hnat : (2121997101 : ℕ)^4635*25000000000000^3611 ≤ 8320701149973^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121997101 5000000000 8320701149973 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1122563999/2500000000 : ℝ)^4635 ≤ (715637099373/2000000000000 : ℝ)^3611 := by
    have hnat : (1122563999 : ℕ)^4635*2000000000000^3611 ≤ 715637099373^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122563999 2500000000 715637099373 2000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32071371/80000000 : ℝ)^4635 ≤ (30935340420977/100000000000000 : ℝ)^3611 := by
    have hnat : (32071371 : ℕ)^4635*100000000000000^3611 ≤ 30935340420977^3611*80000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32071371 80000000 30935340420977 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121997101/5000000000 : ℝ), (1122563999/2500000000 : ℝ), (32071371/80000000 : ℝ)] ![(8320701149973/25000000000000 : ℝ), (715637099373/2000000000000 : ℝ), (30935340420977/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121997101/5000000000 : ℝ)|^4635 ≤ (8320701149973/25000000000000 : ℝ)^3611
        have hw : |(2121997101/5000000000 : ℝ)|=(2121997101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1122563999/2500000000 : ℝ)|^4635 ≤ (715637099373/2000000000000 : ℝ)^3611
        have hw : |(1122563999/2500000000 : ℝ)|=(1122563999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32071371/80000000 : ℝ)|^4635 ≤ (30935340420977/100000000000000 : ℝ)^3611
        have hw : |(32071371/80000000 : ℝ)|=(32071371/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1569_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (97/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2223/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (97/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (97/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (97/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (97/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (97/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (97/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2217/20000 : ℝ) ^ (4633/1024 : ℝ) ≤ (2382093260971081/50000000000000000000 : ℝ) := by
    have hpowers : (2217/20000 : ℝ)^4633 ≤ (2382093260971081/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2217 : ℕ)^4633*50000000000000000000^1024 ≤ 2382093260971081^1024*20000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2217 20000 2382093260971081 50000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2217/20000 : ℝ)) (X := (2382093260971081/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (97/625 : ℝ) ^ (4633/1024 : ℝ) ≤ (5460081366385753/25000000000000000000 : ℝ) := by
    have hpowers : (97/625 : ℝ)^4633 ≤ (5460081366385753/25000000000000000000 : ℝ)^1024 := by
      have hnat : (97 : ℕ)^4633*25000000000000000000^1024 ≤ 5460081366385753^1024*625^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97 625 5460081366385753 25000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (97/625 : ℝ)) (X := (5460081366385753/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002382093260971081/25000000000000000000 : ℝ) ≤ (5000105295617467/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (25002382093260971081/25000000000000000000 : ℝ)^1024 ≤ (5000105295617467/5000000000000000 : ℝ)^4633 := by
      have hnat : (25002382093260971081 : ℕ)^1024*5000000000000000^4633 ≤ 5000105295617467^4633*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002382093260971081 25000000000000000000 5000105295617467 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000105295617467/5000000000000000 : ℝ)) (X := (25002382093260971081/25000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013302255993742587/50000000000000000000 : ℝ) ≤ (2500146990059129/2500000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50013302255993742587/50000000000000000000 : ℝ)^1024 ≤ (2500146990059129/2500000000000000 : ℝ)^4633 := by
      have hnat : (50013302255993742587 : ℕ)^1024*2500000000000000^4633 ≤ 2500146990059129^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013302255993742587 50000000000000000000 2500146990059129 2500000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500146990059129/2500000000000000 : ℝ)) (X := (50013302255993742587/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505460081366385753/12500000000000000000 : ℝ) ≤ (5000482664619049/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (12505460081366385753/12500000000000000000 : ℝ)^1024 ≤ (5000482664619049/5000000000000000 : ℝ)^4633 := by
      have hnat : (12505460081366385753 : ℕ)^1024*5000000000000000^4633 ≤ 5000482664619049^4633*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505460081366385753 12500000000000000000 5000482664619049 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000482664619049/5000000000000000 : ℝ)) (X := (12505460081366385753/12500000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2382093260971081/50000000000000000000 : ℝ) ≤ ((886851354027237187/887000000000000000 : ℝ)+2*(188684500791/221750000000000 : ℝ)*(2217/20000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (886851354027237187/887000000000000000 : ℝ)+2*(188684500791/221750000000000 : ℝ)*(2217/20000 : ℝ)=(5000105295617467/5000000000000000 : ℝ) by norm_num, show 1+2*(2382093260971081/50000000000000000000 : ℝ)=(25002382093260971081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5460081366385753/25000000000000000000 : ℝ)+(2382093260971081/50000000000000000000 : ℝ) ≤ ((886851354027237187/887000000000000000 : ℝ)+(188684500791/221750000000000 : ℝ)*((97/625 : ℝ)+(2217/20000 : ℝ)))^(4633/1024 : ℝ) := by
    rw [show (886851354027237187/887000000000000000 : ℝ)+(188684500791/221750000000000 : ℝ)*((97/625 : ℝ)+(2217/20000 : ℝ))=(2500146990059129/2500000000000000 : ℝ) by norm_num, show 1+(5460081366385753/25000000000000000000 : ℝ)+(2382093260971081/50000000000000000000 : ℝ)=(50013302255993742587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5460081366385753/25000000000000000000 : ℝ) ≤ ((886851354027237187/887000000000000000 : ℝ)+2*(188684500791/221750000000000 : ℝ)*(97/625 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (886851354027237187/887000000000000000 : ℝ)+2*(188684500791/221750000000000 : ℝ)*(97/625 : ℝ)=(5000482664619049/5000000000000000 : ℝ) by norm_num, show 1+2*(5460081366385753/25000000000000000000 : ℝ)=(12505460081366385753/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (886851354027237187/887000000000000000 : ℝ)*(X 1 0+X 2 0)+(188684500791/221750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (97/625 : ℝ)) (c := (886851354027237187/887000000000000000 : ℝ)) (alpha := (188684500791/221750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (886851354027237187/887000000000000000 : ℝ)*(X 0 1+X 2 1)+(188684500791/221750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (97/625 : ℝ)) (c := (886851354027237187/887000000000000000 : ℝ)) (alpha := (188684500791/221750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (886851354027237187/887000000000000000 : ℝ)*(X 0 2+X 1 2)+(188684500791/221750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (97/625 : ℝ)) (c := (886851354027237187/887000000000000000 : ℝ)) (alpha := (188684500791/221750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1786957167/10000000000 : ℝ)*X 0 0+(169565097/312500000 : ℝ)*X 0 1+(1043975669/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337074027/2500000000 : ℝ)*X 1 0+(-473113523/2500000000 : ℝ)*X 1 1+(1043975667/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674148053/5000000000 : ℝ)*X 2 0+(5219878351/10000000000 : ℝ)*X 2 1+(-946227037/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1060982669/2500000000 : ℝ)*X 0 0+(2003182777/5000000000 : ℝ)*X 0 1+(2246396517/5000000000 : ℝ)*X 0 2+(1060982669/2500000000 : ℝ)*X 1 0+(2003182777/5000000000 : ℝ)*X 1 1+(2246396517/5000000000 : ℝ)*X 1 2+(1060982669/2500000000 : ℝ)*X 2 0+(2003182777/5000000000 : ℝ)*X 2 1+(2246396517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1786984109/10000000000 : ℝ)*X 0 0+(652619229/1250000000 : ℝ)*X 0 1+(1356249911/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293747097/10000000000 : ℝ)*X 1 0+(-1687332793/10000000000 : ℝ)*X 1 1+(2712499823/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165429597/312500000 : ℝ)*X 2 0+(2712499821/5000000000 : ℝ)*X 2 1+(-1687332789/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2121997101/5000000000 : ℝ)*X 0 0+(1122563999/2500000000 : ℝ)*X 0 1+(32071371/80000000 : ℝ)*X 0 2+(2121997101/5000000000 : ℝ)*X 1 0+(1122563999/2500000000 : ℝ)*X 1 1+(32071371/80000000 : ℝ)*X 1 2+(2121997101/5000000000 : ℝ)*X 2 0+(1122563999/2500000000 : ℝ)*X 2 1+(32071371/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (131064149896578732402339/22175000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31854397/3125000000000 : ℝ)*(base19) + (118706289/12500000000000 : ℝ)*(base23) + (36302569/100000000000000 : ℝ)*(lower2) + (68580793/50000000000000 : ℝ)*(upper3) + (106398417/100000000000000 : ℝ)*(upper5) + (3452700793172747/100000000000000 : ℝ)*(major0) + (3452700793172747/100000000000000 : ℝ)*(major1) + (3452700793172747/100000000000000 : ℝ)*(major2) + (606195688271847/12500000000000 : ℝ)*(sp0) + (484958131814761/10000000000000 : ℝ)*(sp1) + (4849581387838003/100000000000000 : ℝ)*(sp2) + (2055811670108793/100000000000000 : ℝ)*(sp3) + (16831313539/100000000000000 : ℝ)*(sp4) + (7381733499/100000000000000 : ℝ)*(sp7) + (513954762960573/25000000000000 : ℝ)*(f.failure) + (2424791168744157/50000000000000 : ℝ)*(f.sum) + (115281939563229/22175000000000000000000000000 : ℝ)*base65 + (141821320793749311/88700000000000000000000000000000 : ℝ)*base68 + (264852872665249311/88700000000000000000000000000000 : ℝ)*base70 + (552117251234650689/88700000000000000000000000000000 : ℝ)*base71 + (5417806833463/2771875000000000000000000000 : ℝ)*base73 + (53394158357049311/88700000000000000000000000000000 : ℝ)*base76 + (120040530584050689/88700000000000000000000000000000 : ℝ)*base77 + (53792612087550689/88700000000000000000000000000000 : ℝ)*base79 + (20816897654379/22175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (11928473/2500000000000000000000 : ℝ)*base90 + (11928473/2500000000000000000000 : ℝ)*base92 + (11928473/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (159853738351620874689190173/22175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1152001157/100000000000000 : ℝ)*(base19) + (62057843/5000000000000 : ℝ)*(base23) + (36741131/25000000000000 : ℝ)*(upper3) + (38034489/100000000000000 : ℝ)*(lower4) + (78519091/50000000000000 : ℝ)*(upper5) + (3489208278692093/100000000000000 : ℝ)*(major0) + (3489208278692093/100000000000000 : ℝ)*(major1) + (3489208278692093/100000000000000 : ℝ)*(major2) + (18577114977/100000000000000 : ℝ)*(sp1) + (2453482351/12500000000000 : ℝ)*(sp2) + (4900859851915011/100000000000000 : ℝ)*(sp4) + (4900840122798877/100000000000000 : ℝ)*(sp5) + (4900838982899343/100000000000000 : ℝ)*(sp6) + (259694558147243/12500000000000 : ℝ)*(sp7) + (259694558147243/12500000000000 : ℝ)*(f.failure) + (4900859851915011/100000000000000 : ℝ)*(f.sum) + (56310581047551/22175000000000000000000000000 : ℝ)*base65 + (110651329716485609/88700000000000000000000000000000 : ℝ)*base68 + (699813113316085609/88700000000000000000000000000000 : ℝ)*base70 + (687491148219614391/88700000000000000000000000000000 : ℝ)*base71 + (78254464549301/22175000000000000000000000000 : ℝ)*base73 + (886727496907185609/88700000000000000000000000000000 : ℝ)*base76 + (774527422774885609/88700000000000000000000000000000 : ℝ)*base78 + (25688142035885609/88700000000000000000000000000000 : ℝ)*base80 + (47791976417549/22175000000000000000000000000 : ℝ)*base82 + (2543857/1250000000000000000000 : ℝ)*base89 + (2543857/1250000000000000000000 : ℝ)*base91 + (2543857/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1569_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (97/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1569_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1569_s5_0 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1786979857/10000000000 : ℝ)*x 0 + (339120419/625000000 : ℝ)*x 1 + (5220019729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1786979857/10000000000 : ℝ)^4635 ≤ (1370715396469/12500000000000 : ℝ)^3611 := by
    have hnat : (1786979857 : ℕ)^4635*12500000000000^3611 ≤ 1370715396469^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786979857 10000000000 1370715396469 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339120419/625000000 : ℝ)^4635 ≤ (22811118722641/50000000000000 : ℝ)^3611 := by
    have hnat : (339120419 : ℕ)^4635*50000000000000^3611 ≤ 22811118722641^3611*625000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339120419 625000000 22811118722641 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220019729/10000000000 : ℝ)^4635 ≤ (10853009841061/25000000000000 : ℝ)^3611 := by
    have hnat : (5220019729 : ℕ)^4635*25000000000000^3611 ≤ 10853009841061^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220019729 10000000000 10853009841061 25000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1786979857/10000000000 : ℝ), (339120419/625000000 : ℝ), (5220019729/10000000000 : ℝ)] ![(1370715396469/12500000000000 : ℝ), (22811118722641/50000000000000 : ℝ), (10853009841061/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1786979857/10000000000 : ℝ)|^4635 ≤ (1370715396469/12500000000000 : ℝ)^3611
        have hw : |(-1786979857/10000000000 : ℝ)|=(1786979857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339120419/625000000 : ℝ)|^4635 ≤ (22811118722641/50000000000000 : ℝ)^3611
        have hw : |(339120419/625000000 : ℝ)|=(339120419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220019729/10000000000 : ℝ)|^4635 ≤ (10853009841061/25000000000000 : ℝ)^3611
        have hw : |(5220019729/10000000000 : ℝ)|=(5220019729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s5_1 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267412741/500000000 : ℝ)*x 0 + (-946160493/5000000000 : ℝ)*x 1 + (2610009867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267412741/500000000 : ℝ)^4635 ≤ (44785665445401/100000000000000 : ℝ)^3611 := by
    have hnat : (267412741 : ℕ)^4635*100000000000000^3611 ≤ 44785665445401^3611*500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267412741 500000000 44785665445401 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946160493/5000000000 : ℝ)^4635 ≤ (11802295128553/100000000000000 : ℝ)^3611 := by
    have hnat : (946160493 : ℕ)^4635*100000000000000^3611 ≤ 11802295128553^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946160493 5000000000 11802295128553 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610009867/5000000000 : ℝ)^4635 ≤ (21706019708809/50000000000000 : ℝ)^3611 := by
    have hnat : (2610009867 : ℕ)^4635*50000000000000^3611 ≤ 21706019708809^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610009867 5000000000 21706019708809 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267412741/500000000 : ℝ), (-946160493/5000000000 : ℝ), (2610009867/5000000000 : ℝ)] ![(44785665445401/100000000000000 : ℝ), (11802295128553/100000000000000 : ℝ), (21706019708809/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267412741/500000000 : ℝ)|^4635 ≤ (44785665445401/100000000000000 : ℝ)^3611
        have hw : |(267412741/500000000 : ℝ)|=(267412741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-946160493/5000000000 : ℝ)|^4635 ≤ (11802295128553/100000000000000 : ℝ)^3611
        have hw : |(-946160493/5000000000 : ℝ)|=(946160493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610009867/5000000000 : ℝ)|^4635 ≤ (21706019708809/50000000000000 : ℝ)^3611
        have hw : |(2610009867/5000000000 : ℝ)|=(2610009867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s5_2 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348254823/10000000000 : ℝ)*x 0 + (1305004933/2500000000 : ℝ)*x 1 + (-236540123/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348254823/10000000000 : ℝ)^4635 ≤ (44785665477647/100000000000000 : ℝ)^3611 := by
    have hnat : (5348254823 : ℕ)^4635*100000000000000^3611 ≤ 44785665477647^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348254823 10000000000 44785665477647 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305004933/2500000000 : ℝ)^4635 ≤ (43412039396269/100000000000000 : ℝ)^3611 := by
    have hnat : (1305004933 : ℕ)^4635*100000000000000^3611 ≤ 43412039396269^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305004933 2500000000 43412039396269 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236540123/1250000000 : ℝ)^4635 ≤ (5901147556271/50000000000000 : ℝ)^3611 := by
    have hnat : (236540123 : ℕ)^4635*50000000000000^3611 ≤ 5901147556271^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236540123 1250000000 5901147556271 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348254823/10000000000 : ℝ), (1305004933/2500000000 : ℝ), (-236540123/1250000000 : ℝ)] ![(44785665477647/100000000000000 : ℝ), (43412039396269/100000000000000 : ℝ), (5901147556271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348254823/10000000000 : ℝ)|^4635 ≤ (44785665477647/100000000000000 : ℝ)^3611
        have hw : |(5348254823/10000000000 : ℝ)|=(5348254823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305004933/2500000000 : ℝ)|^4635 ≤ (43412039396269/100000000000000 : ℝ)^3611
        have hw : |(1305004933/2500000000 : ℝ)|=(1305004933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-236540123/1250000000 : ℝ)|^4635 ≤ (5901147556271/50000000000000 : ℝ)^3611
        have hw : |(-236540123/1250000000 : ℝ)|=(236540123/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s5_3 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243945333/10000000000 : ℝ)*x 0 + (2003357569/5000000000 : ℝ)*x 1 + (2246220099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243945333/10000000000 : ℝ)^4635 ≤ (4160289084187/12500000000000 : ℝ)^3611 := by
    have hnat : (4243945333 : ℕ)^4635*12500000000000^3611 ≤ 4160289084187^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243945333 10000000000 4160289084187 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003357569/5000000000 : ℝ)^4635 ≤ (30913489593891/100000000000000 : ℝ)^3611 := by
    have hnat : (2003357569 : ℕ)^4635*100000000000000^3611 ≤ 30913489593891^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003357569 5000000000 30913489593891 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246220099/5000000000 : ℝ)^4635 ≤ (17902098862491/50000000000000 : ℝ)^3611 := by
    have hnat : (2246220099 : ℕ)^4635*50000000000000^3611 ≤ 17902098862491^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246220099 5000000000 17902098862491 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243945333/10000000000 : ℝ), (2003357569/5000000000 : ℝ), (2246220099/5000000000 : ℝ)] ![(4160289084187/12500000000000 : ℝ), (30913489593891/100000000000000 : ℝ), (17902098862491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243945333/10000000000 : ℝ)|^4635 ≤ (4160289084187/12500000000000 : ℝ)^3611
        have hw : |(4243945333/10000000000 : ℝ)|=(4243945333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2003357569/5000000000 : ℝ)|^4635 ≤ (30913489593891/100000000000000 : ℝ)^3611
        have hw : |(2003357569/5000000000 : ℝ)|=(2003357569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246220099/5000000000 : ℝ)|^4635 ≤ (17902098862491/50000000000000 : ℝ)^3611
        have hw : |(2246220099/5000000000 : ℝ)|=(2246220099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s5_4 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-35740133/200000000 : ℝ)*x 0 + (5221092143/10000000000 : ℝ)*x 1 + (678105797/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (35740133/200000000 : ℝ)^4635 ≤ (10965934210469/100000000000000 : ℝ)^3611 := by
    have hnat : (35740133 : ℕ)^4635*100000000000000^3611 ≤ 10965934210469^3611*200000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35740133 200000000 10965934210469 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221092143/10000000000 : ℝ)^4635 ≤ (21711743758539/50000000000000 : ℝ)^3611 := by
    have hnat : (5221092143 : ℕ)^4635*50000000000000^3611 ≤ 21711743758539^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221092143 10000000000 21711743758539 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678105797/1250000000 : ℝ)^4635 ≤ (45610578257991/100000000000000 : ℝ)^3611 := by
    have hnat : (678105797 : ℕ)^4635*100000000000000^3611 ≤ 45610578257991^3611*1250000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678105797 1250000000 45610578257991 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-35740133/200000000 : ℝ), (5221092143/10000000000 : ℝ), (678105797/1250000000 : ℝ)] ![(10965934210469/100000000000000 : ℝ), (21711743758539/50000000000000 : ℝ), (45610578257991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-35740133/200000000 : ℝ)|^4635 ≤ (10965934210469/100000000000000 : ℝ)^3611
        have hw : |(-35740133/200000000 : ℝ)|=(35740133/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221092143/10000000000 : ℝ)|^4635 ≤ (21711743758539/50000000000000 : ℝ)^3611
        have hw : |(5221092143/10000000000 : ℝ)|=(5221092143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678105797/1250000000 : ℝ)|^4635 ≤ (45610578257991/100000000000000 : ℝ)^3611
        have hw : |(678105797/1250000000 : ℝ)|=(678105797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s5_5 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293784597/10000000000 : ℝ)*x 0 + (-421873587/2500000000 : ℝ)*x 1 + (2712423197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293784597/10000000000 : ℝ)^4635 ≤ (22100518997917/50000000000000 : ℝ)^3611 := by
    have hnat : (5293784597 : ℕ)^4635*50000000000000^3611 ≤ 22100518997917^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293784597 10000000000 22100518997917 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421873587/2500000000 : ℝ)^4635 ≤ (5094191767089/50000000000000 : ℝ)^3611 := by
    have hnat : (421873587 : ℕ)^4635*50000000000000^3611 ≤ 5094191767089^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421873587 2500000000 5094191767089 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712423197/5000000000 : ℝ)^4635 ≤ (22805289226123/50000000000000 : ℝ)^3611 := by
    have hnat : (2712423197 : ℕ)^4635*50000000000000^3611 ≤ 22805289226123^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712423197 5000000000 22805289226123 50000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293784597/10000000000 : ℝ), (-421873587/2500000000 : ℝ), (2712423197/5000000000 : ℝ)] ![(22100518997917/50000000000000 : ℝ), (5094191767089/50000000000000 : ℝ), (22805289226123/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293784597/10000000000 : ℝ)|^4635 ≤ (22100518997917/50000000000000 : ℝ)^3611
        have hw : |(5293784597/10000000000 : ℝ)|=(5293784597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421873587/2500000000 : ℝ)|^4635 ≤ (5094191767089/50000000000000 : ℝ)^3611
        have hw : |(-421873587/2500000000 : ℝ)|=(421873587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712423197/5000000000 : ℝ)|^4635 ≤ (22805289226123/50000000000000 : ℝ)^3611
        have hw : |(2712423197/5000000000 : ℝ)|=(2712423197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s5_6 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323446151/2500000000 : ℝ)*x 0 + (2712423203/5000000000 : ℝ)*x 1 + (-1687494321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323446151/2500000000 : ℝ)^4635 ≤ (5525129758857/12500000000000 : ℝ)^3611 := by
    have hnat : (1323446151 : ℕ)^4635*12500000000000^3611 ≤ 5525129758857^3611*2500000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323446151 2500000000 5525129758857 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2712423203/5000000000 : ℝ)^4635 ≤ (182442314327/400000000000 : ℝ)^3611 := by
    have hnat : (2712423203 : ℕ)^4635*400000000000^3611 ≤ 182442314327^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712423203 5000000000 182442314327 400000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1687494321/10000000000 : ℝ)^4635 ≤ (1273547915617/12500000000000 : ℝ)^3611 := by
    have hnat : (1687494321 : ℕ)^4635*12500000000000^3611 ≤ 1273547915617^3611*10000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687494321 10000000000 1273547915617 12500000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323446151/2500000000 : ℝ), (2712423203/5000000000 : ℝ), (-1687494321/10000000000 : ℝ)] ![(5525129758857/12500000000000 : ℝ), (182442314327/400000000000 : ℝ), (1273547915617/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323446151/2500000000 : ℝ)|^4635 ≤ (5525129758857/12500000000000 : ℝ)^3611
        have hw : |(1323446151/2500000000 : ℝ)|=(1323446151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2712423203/5000000000 : ℝ)|^4635 ≤ (182442314327/400000000000 : ℝ)^3611
        have hw : |(2712423203/5000000000 : ℝ)|=(2712423203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1687494321/10000000000 : ℝ)|^4635 ≤ (1273547915617/12500000000000 : ℝ)^3611
        have hw : |(-1687494321/10000000000 : ℝ)|=(1687494321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1569_s5_7 (p : ℝ) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (424400859/1000000000 : ℝ)*x 0 + (2244955233/5000000000 : ℝ)*x 1 + (801852713/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424400859/1000000000 : ℝ)^4635 ≤ (33282949433057/100000000000000 : ℝ)^3611 := by
    have hnat : (424400859 : ℕ)^4635*100000000000000^3611 ≤ 33282949433057^3611*1000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424400859 1000000000 33282949433057 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244955233/5000000000 : ℝ)^4635 ≤ (35778320736923/100000000000000 : ℝ)^3611 := by
    have hnat : (2244955233 : ℕ)^4635*100000000000000^3611 ≤ 35778320736923^3611*5000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244955233 5000000000 35778320736923 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (801852713/2000000000 : ℝ)^4635 ≤ (30938729815947/100000000000000 : ℝ)^3611 := by
    have hnat : (801852713 : ℕ)^4635*100000000000000^3611 ≤ 30938729815947^3611*2000000000^4635 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      801852713 2000000000 30938729815947 100000000000000 4635 3611 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4635/1024 : ℝ)) 4635 3611 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424400859/1000000000 : ℝ), (2244955233/5000000000 : ℝ), (801852713/2000000000 : ℝ)] ![(33282949433057/100000000000000 : ℝ), (35778320736923/100000000000000 : ℝ), (30938729815947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424400859/1000000000 : ℝ)|^4635 ≤ (33282949433057/100000000000000 : ℝ)^3611
        have hw : |(424400859/1000000000 : ℝ)|=(424400859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244955233/5000000000 : ℝ)|^4635 ≤ (35778320736923/100000000000000 : ℝ)^3611
        have hw : |(2244955233/5000000000 : ℝ)|=(2244955233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(801852713/2000000000 : ℝ)|^4635 ≤ (30938729815947/100000000000000 : ℝ)^3611
        have hw : |(801852713/2000000000 : ℝ)|=(801852713/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1569_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5559/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2223/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2223/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2223/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2223/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2223/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2223/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2223/20000 : ℝ) ^ (4633/1024 : ℝ) ≤ (4822801371627463/100000000000000000000 : ℝ) := by
    have hpowers : (2223/20000 : ℝ)^4633 ≤ (4822801371627463/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2223 : ℕ)^4633*100000000000000000000^1024 ≤ 4822801371627463^1024*20000^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2223 20000 4822801371627463 100000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2223/20000 : ℝ)) (X := (4822801371627463/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4633/1024 : ℝ) ≤ (21637322860964751/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4633 ≤ (21637322860964751/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4633*100000000000000000000^1024 ≤ 21637322860964751^1024*3125^4633 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 21637322860964751 100000000000000000000 4633 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (21637322860964751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004822801371627463/50000000000000000000 : ℝ) ≤ (200004263641771/200000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50004822801371627463/50000000000000000000 : ℝ)^1024 ≤ (200004263641771/200000000000000 : ℝ)^4633 := by
      have hnat : (50004822801371627463 : ℕ)^1024*200000000000000^4633 ≤ 200004263641771^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004822801371627463 50000000000000000000 200004263641771 200000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200004263641771/200000000000000 : ℝ)) (X := (50004822801371627463/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013230062116296107/50000000000000000000 : ℝ) ≤ (2500146192398273/2500000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50013230062116296107/50000000000000000000 : ℝ)^1024 ≤ (2500146192398273/2500000000000000 : ℝ)^4633 := by
      have hnat : (50013230062116296107 : ℕ)^1024*2500000000000000^4633 ≤ 2500146192398273^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013230062116296107 50000000000000000000 2500146192398273 2500000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500146192398273/2500000000000000 : ℝ)) (X := (50013230062116296107/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021637322860964751/50000000000000000000 : ℝ) ≤ (5000478178548817/5000000000000000 : ℝ) ^ (4633/1024 : ℝ) := by
    have hpowers : (50021637322860964751/50000000000000000000 : ℝ)^1024 ≤ (5000478178548817/5000000000000000 : ℝ)^4633 := by
      have hnat : (50021637322860964751 : ℕ)^1024*5000000000000000^4633 ≤ 5000478178548817^4633*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021637322860964751 50000000000000000000 5000478178548817 5000000000000000 1024 4633 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000478178548817/5000000000000000 : ℝ)) (X := (50021637322860964751/50000000000000000000 : ℝ)) (by norm_num) 4633 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4822801371627463/100000000000000000000 : ℝ) ≤ ((4372267185504726049/4373000000000000000 : ℝ)+2*(185793752271/218650000000000 : ℝ)*(2223/20000 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (4372267185504726049/4373000000000000000 : ℝ)+2*(185793752271/218650000000000 : ℝ)*(2223/20000 : ℝ)=(200004263641771/200000000000000 : ℝ) by norm_num, show 1+2*(4822801371627463/100000000000000000000 : ℝ)=(50004822801371627463/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21637322860964751/100000000000000000000 : ℝ)+(4822801371627463/100000000000000000000 : ℝ) ≤ ((4372267185504726049/4373000000000000000 : ℝ)+(185793752271/218650000000000 : ℝ)*((484/3125 : ℝ)+(2223/20000 : ℝ)))^(4633/1024 : ℝ) := by
    rw [show (4372267185504726049/4373000000000000000 : ℝ)+(185793752271/218650000000000 : ℝ)*((484/3125 : ℝ)+(2223/20000 : ℝ))=(2500146192398273/2500000000000000 : ℝ) by norm_num, show 1+(21637322860964751/100000000000000000000 : ℝ)+(4822801371627463/100000000000000000000 : ℝ)=(50013230062116296107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21637322860964751/100000000000000000000 : ℝ) ≤ ((4372267185504726049/4373000000000000000 : ℝ)+2*(185793752271/218650000000000 : ℝ)*(484/3125 : ℝ))^(4633/1024 : ℝ) := by
    rw [show (4372267185504726049/4373000000000000000 : ℝ)+2*(185793752271/218650000000000 : ℝ)*(484/3125 : ℝ)=(5000478178548817/5000000000000000 : ℝ) by norm_num, show 1+2*(21637322860964751/100000000000000000000 : ℝ)=(50021637322860964751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4372267185504726049/4373000000000000000 : ℝ)*(X 1 0+X 2 0)+(185793752271/218650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (4372267185504726049/4373000000000000000 : ℝ)) (alpha := (185793752271/218650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4372267185504726049/4373000000000000000 : ℝ)*(X 0 1+X 2 1)+(185793752271/218650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (4372267185504726049/4373000000000000000 : ℝ)) (alpha := (185793752271/218650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4372267185504726049/4373000000000000000 : ℝ)*(X 0 2+X 1 2)+(185793752271/218650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4633/1024 : ℝ)) (lo := (2223/20000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (4372267185504726049/4373000000000000000 : ℝ)) (alpha := (185793752271/218650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1786979857/10000000000 : ℝ)*X 0 0+(339120419/625000000 : ℝ)*X 0 1+(5220019729/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267412741/500000000 : ℝ)*X 1 0+(-946160493/5000000000 : ℝ)*X 1 1+(2610009867/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348254823/10000000000 : ℝ)*X 2 0+(1305004933/2500000000 : ℝ)*X 2 1+(-236540123/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4243945333/10000000000 : ℝ)*X 0 0+(2003357569/5000000000 : ℝ)*X 0 1+(2246220099/5000000000 : ℝ)*X 0 2+(4243945333/10000000000 : ℝ)*X 1 0+(2003357569/5000000000 : ℝ)*X 1 1+(2246220099/5000000000 : ℝ)*X 1 2+(4243945333/10000000000 : ℝ)*X 2 0+(2003357569/5000000000 : ℝ)*X 2 1+(2246220099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-35740133/200000000 : ℝ)*X 0 0+(5221092143/10000000000 : ℝ)*X 0 1+(678105797/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293784597/10000000000 : ℝ)*X 1 0+(-421873587/2500000000 : ℝ)*X 1 1+(2712423197/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323446151/2500000000 : ℝ)*X 2 0+(2712423203/5000000000 : ℝ)*X 2 1+(-1687494321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((424400859/1000000000 : ℝ)*X 0 0+(2244955233/5000000000 : ℝ)*X 0 1+(801852713/2000000000 : ℝ)*X 0 2+(424400859/1000000000 : ℝ)*X 1 0+(2244955233/5000000000 : ℝ)*X 1 1+(801852713/2000000000 : ℝ)*X 1 2+(424400859/1000000000 : ℝ)*X 2 0+(2244955233/5000000000 : ℝ)*X 2 1+(801852713/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1569_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34203046736918482622365143/5466250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (527144021/50000000000000 : ℝ)*(base19) + (197210311/20000000000000 : ℝ)*(base23) + (37951591/100000000000000 : ℝ)*(lower2) + (30722299/20000000000000 : ℝ)*(upper3) + (52364769/50000000000000 : ℝ)*(upper5) + (172884749401569/5000000000000 : ℝ)*(major0) + (172884749401569/5000000000000 : ℝ)*(major1) + (172884749401569/5000000000000 : ℝ)*(major2) + (4856579832284229/100000000000000 : ℝ)*(sp0) + (4856596000579837/100000000000000 : ℝ)*(sp1) + (1214149017204081/25000000000000 : ℝ)*(sp2) + (514696216366267/25000000000000 : ℝ)*(sp3) + (344451673/2000000000000 : ℝ)*(sp4) + (1961789687/25000000000000 : ℝ)*(sp7) + (257349089077977/12500000000000 : ℝ)*(f.failure) + (4856597054867879/100000000000000 : ℝ)*(f.sum) + (18162638642111/4373000000000000000000000000 : ℝ)*base66 + (88772537465319119/21865000000000000000000000000000 : ℝ)*base68 + (61584662982874119/21865000000000000000000000000000 : ℝ)*base70 + (64928059352209119/21865000000000000000000000000000 : ℝ)*base72 + (1664953283841/2186500000000000000000000000 : ℝ)*base73 + (258535771759579119/21865000000000000000000000000000 : ℝ)*base76 + (36592469264089119/21865000000000000000000000000000 : ℝ)*base78 + (30625842910950881/21865000000000000000000000000000 : ℝ)*base79 + (3516013346843/1093250000000000000000000000 : ℝ)*base82 + (18724923/1250000000000000000000 : ℝ)*base89 + (18724923/1250000000000000000000 : ℝ)*base91 + (18724923/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44836090493140052042259/4373000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1538816817/100000000000000 : ℝ)*(base19) + (1714880301/100000000000000 : ℝ)*(base23) + (251013639/50000000000000 : ℝ)*(lower1) + (21083917/10000000000000 : ℝ)*(upper3) + (72897913/100000000000000 : ℝ)*(lower4) + (51059249/25000000000000 : ℝ)*(upper5) + (34941831977457/1000000000000 : ℝ)*(major0) + (34941831977457/1000000000000 : ℝ)*(major1) + (34941831977457/1000000000000 : ℝ)*(major2) + (1548626411/50000000000000 : ℝ)*(sp2) + (4907847405033887/100000000000000 : ℝ)*(sp4) + (490784586621707/10000000000000 : ℝ)*(sp5) + (1226960648225191/25000000000000 : ℝ)*(sp6) + (520129662173237/25000000000000 : ℝ)*(sp7) + (520129662173237/25000000000000 : ℝ)*(f.failure) + (4907847405033887/100000000000000 : ℝ)*(f.sum) + (808066477533/437300000000000000000000000 : ℝ)*base66 + (135847772876539607/4373000000000000000000000000000 : ℝ)*base68 + (20624116489381393/4373000000000000000000000000000 : ℝ)*base69 + (297175835117412607/4373000000000000000000000000000 : ℝ)*base72 + (1359594377413/546625000000000000000000000 : ℝ)*base74 + (340417769353982607/4373000000000000000000000000000 : ℝ)*base76 + (10462846859431393/4373000000000000000000000000000 : ℝ)*base77 + (37024403493929393/4373000000000000000000000000000 : ℝ)*base79 + (395450310373/136656250000000000000000000 : ℝ)*base81 + (6468337/2500000000000000000000 : ℝ)*base90 + (6468337/2500000000000000000000 : ℝ)*base92 + (6468337/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1569_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2223/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1569_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1569_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7907/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1569_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1569_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1569_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4633/1024 : ℝ) ≤ p) (hpb : p ≤ (4635/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167947699/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7907/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5407/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5559/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1569_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
