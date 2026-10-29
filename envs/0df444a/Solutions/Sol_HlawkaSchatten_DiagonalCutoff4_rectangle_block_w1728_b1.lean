-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1728_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:05:49.734247+00:00
-- url     : https://prove2.me/submissions/9200fec6-6c80-41f1-97f9-c92ca233dc9f

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
theorem support_rectangle_w1728_s3_0 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-337402097/2500000000 : ℝ)*x 0 + (341174049/625000000 : ℝ)*x 1 + (5140189407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337402097/2500000000 : ℝ)^5447 ≤ (8488599038357/100000000000000 : ℝ)^4423 := by
    have hnat : (337402097 : ℕ)^5447*100000000000000^4423 ≤ 8488599038357^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337402097 2500000000 8488599038357 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341174049/625000000 : ℝ)^5447 ≤ (11862308401949/25000000000000 : ℝ)^4423 := by
    have hnat : (341174049 : ℕ)^5447*25000000000000^4423 ≤ 11862308401949^4423*625000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341174049 625000000 11862308401949 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140189407/10000000000 : ℝ)^5447 ≤ (5507770917859/12500000000000 : ℝ)^4423 := by
    have hnat : (5140189407 : ℕ)^5447*12500000000000^4423 ≤ 5507770917859^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140189407 10000000000 5507770917859 12500000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-337402097/2500000000 : ℝ), (341174049/625000000 : ℝ), (5140189407/10000000000 : ℝ)] ![(8488599038357/100000000000000 : ℝ), (11862308401949/25000000000000 : ℝ), (5507770917859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-337402097/2500000000 : ℝ)|^5447 ≤ (8488599038357/100000000000000 : ℝ)^4423
        have hw : |(-337402097/2500000000 : ℝ)|=(337402097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341174049/625000000 : ℝ)|^5447 ≤ (11862308401949/25000000000000 : ℝ)^4423
        have hw : |(341174049/625000000 : ℝ)|=(341174049/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140189407/10000000000 : ℝ)|^5447 ≤ (5507770917859/12500000000000 : ℝ)^4423
        have hw : |(5140189407/10000000000 : ℝ)|=(5140189407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s3_1 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337465041/10000000000 : ℝ)*x 0 + (-1514572427/10000000000 : ℝ)*x 1 + (5140189477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337465041/10000000000 : ℝ)^5447 ≤ (11538476248633/25000000000000 : ℝ)^4423 := by
    have hnat : (5337465041 : ℕ)^5447*25000000000000^4423 ≤ 11538476248633^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337465041 10000000000 11538476248633 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1514572427/10000000000 : ℝ)^5447 ≤ (9783926906439/100000000000000 : ℝ)^4423 := by
    have hnat : (1514572427 : ℕ)^5447*100000000000000^4423 ≤ 9783926906439^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1514572427 10000000000 9783926906439 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140189477/10000000000 : ℝ)^5447 ≤ (44062168081839/100000000000000 : ℝ)^4423 := by
    have hnat : (5140189477 : ℕ)^5447*100000000000000^4423 ≤ 44062168081839^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140189477 10000000000 44062168081839 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337465041/10000000000 : ℝ), (-1514572427/10000000000 : ℝ), (5140189477/10000000000 : ℝ)] ![(11538476248633/25000000000000 : ℝ), (9783926906439/100000000000000 : ℝ), (44062168081839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337465041/10000000000 : ℝ)|^5447 ≤ (11538476248633/25000000000000 : ℝ)^4423
        have hw : |(5337465041/10000000000 : ℝ)|=(5337465041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1514572427/10000000000 : ℝ)|^5447 ≤ (9783926906439/100000000000000 : ℝ)^4423
        have hw : |(-1514572427/10000000000 : ℝ)|=(1514572427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140189477/10000000000 : ℝ)|^5447 ≤ (44062168081839/100000000000000 : ℝ)^4423
        have hw : |(5140189477/10000000000 : ℝ)|=(5140189477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s3_2 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067493013/2000000000 : ℝ)*x 0 + (25700947/50000000 : ℝ)*x 1 + (-757286249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067493013/2000000000 : ℝ)^5447 ≤ (46153905250111/100000000000000 : ℝ)^4423 := by
    have hnat : (1067493013 : ℕ)^5447*100000000000000^4423 ≤ 46153905250111^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067493013 2000000000 46153905250111 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (25700947/50000000 : ℝ)^5447 ≤ (1762486690759/4000000000000 : ℝ)^4423 := by
    have hnat : (25700947 : ℕ)^5447*4000000000000^4423 ≤ 1762486690759^4423*50000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25700947 50000000 1762486690759 4000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (757286249/5000000000 : ℝ)^5447 ≤ (391357098851/4000000000000 : ℝ)^4423 := by
    have hnat : (757286249 : ℕ)^5447*4000000000000^4423 ≤ 391357098851^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757286249 5000000000 391357098851 4000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067493013/2000000000 : ℝ), (25700947/50000000 : ℝ), (-757286249/5000000000 : ℝ)] ![(46153905250111/100000000000000 : ℝ), (1762486690759/4000000000000 : ℝ), (391357098851/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067493013/2000000000 : ℝ)|^5447 ≤ (46153905250111/100000000000000 : ℝ)^4423
        have hw : |(1067493013/2000000000 : ℝ)|=(1067493013/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(25700947/50000000 : ℝ)|^5447 ≤ (1762486690759/4000000000000 : ℝ)^4423
        have hw : |(25700947/50000000 : ℝ)|=(25700947/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-757286249/5000000000 : ℝ)|^5447 ≤ (391357098851/4000000000000 : ℝ)^4423
        have hw : |(-757286249/5000000000 : ℝ)|=(757286249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s3_3 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1020564527/2500000000 : ℝ)*x 0 + (3618512189/10000000000 : ℝ)*x 1 + (4580211763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020564527/2500000000 : ℝ)^5447 ≤ (8293871141787/25000000000000 : ℝ)^4423 := by
    have hnat : (1020564527 : ℕ)^5447*25000000000000^4423 ≤ 8293871141787^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020564527 2500000000 8293871141787 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3618512189/10000000000 : ℝ)^5447 ≤ (1429855705391/5000000000000 : ℝ)^4423 := by
    have hnat : (3618512189 : ℕ)^5447*5000000000000^4423 ≤ 1429855705391^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3618512189 10000000000 1429855705391 5000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4580211763/10000000000 : ℝ)^5447 ≤ (38227401308843/100000000000000 : ℝ)^4423 := by
    have hnat : (4580211763 : ℕ)^5447*100000000000000^4423 ≤ 38227401308843^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4580211763 10000000000 38227401308843 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020564527/2500000000 : ℝ), (3618512189/10000000000 : ℝ), (4580211763/10000000000 : ℝ)] ![(8293871141787/25000000000000 : ℝ), (1429855705391/5000000000000 : ℝ), (38227401308843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020564527/2500000000 : ℝ)|^5447 ≤ (8293871141787/25000000000000 : ℝ)^4423
        have hw : |(1020564527/2500000000 : ℝ)|=(1020564527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3618512189/10000000000 : ℝ)|^5447 ≤ (1429855705391/5000000000000 : ℝ)^4423
        have hw : |(3618512189/10000000000 : ℝ)|=(3618512189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4580211763/10000000000 : ℝ)|^5447 ≤ (38227401308843/100000000000000 : ℝ)^4423
        have hw : |(4580211763/10000000000 : ℝ)|=(4580211763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s3_4 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-674874883/5000000000 : ℝ)*x 0 + (1028754681/2000000000 : ℝ)*x 1 + (5455147471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (674874883/5000000000 : ℝ)^5447 ≤ (424484707171/5000000000000 : ℝ)^4423 := by
    have hnat : (674874883 : ℕ)^5447*5000000000000^4423 ≤ 424484707171^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674874883 5000000000 424484707171 5000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028754681/2000000000 : ℝ)^5447 ≤ (22050002749863/50000000000000 : ℝ)^4423 := by
    have hnat : (1028754681 : ℕ)^5447*50000000000000^4423 ≤ 22050002749863^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028754681 2000000000 22050002749863 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5455147471/10000000000 : ℝ)^5447 ≤ (9482060068389/20000000000000 : ℝ)^4423 := by
    have hnat : (5455147471 : ℕ)^5447*20000000000000^4423 ≤ 9482060068389^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5455147471 10000000000 9482060068389 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-674874883/5000000000 : ℝ), (1028754681/2000000000 : ℝ), (5455147471/10000000000 : ℝ)] ![(424484707171/5000000000000 : ℝ), (22050002749863/50000000000000 : ℝ), (9482060068389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-674874883/5000000000 : ℝ)|^5447 ≤ (424484707171/5000000000000 : ℝ)^4423
        have hw : |(-674874883/5000000000 : ℝ)|=(674874883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028754681/2000000000 : ℝ)|^5447 ≤ (22050002749863/50000000000000 : ℝ)^4423
        have hw : |(1028754681/2000000000 : ℝ)|=(1028754681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5455147471/10000000000 : ℝ)|^5447 ≤ (9482060068389/20000000000000 : ℝ)^4423
        have hw : |(5455147471/10000000000 : ℝ)|=(5455147471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s3_5 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252194707/10000000000 : ℝ)*x 0 + (-599806953/5000000000 : ℝ)*x 1 + (2727573837/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252194707/10000000000 : ℝ)^5447 ≤ (45247536936949/100000000000000 : ℝ)^4423 := by
    have hnat : (5252194707 : ℕ)^5447*100000000000000^4423 ≤ 45247536936949^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252194707 10000000000 45247536936949 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599806953/5000000000 : ℝ)^5447 ≤ (7342160536497/100000000000000 : ℝ)^4423 := by
    have hnat : (599806953 : ℕ)^5447*100000000000000^4423 ≤ 7342160536497^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599806953 5000000000 7342160536497 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2727573837/5000000000 : ℝ)^5447 ≤ (2370515125733/5000000000000 : ℝ)^4423 := by
    have hnat : (2727573837 : ℕ)^5447*5000000000000^4423 ≤ 2370515125733^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727573837 5000000000 2370515125733 5000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252194707/10000000000 : ℝ), (-599806953/5000000000 : ℝ), (2727573837/5000000000 : ℝ)] ![(45247536936949/100000000000000 : ℝ), (7342160536497/100000000000000 : ℝ), (2370515125733/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252194707/10000000000 : ℝ)|^5447 ≤ (45247536936949/100000000000000 : ℝ)^4423
        have hw : |(5252194707/10000000000 : ℝ)|=(5252194707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-599806953/5000000000 : ℝ)|^5447 ≤ (7342160536497/100000000000000 : ℝ)^4423
        have hw : |(-599806953/5000000000 : ℝ)|=(599806953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2727573837/5000000000 : ℝ)|^5447 ≤ (2370515125733/5000000000000 : ℝ)^4423
        have hw : |(2727573837/5000000000 : ℝ)|=(2727573837/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s3_6 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252194443/10000000000 : ℝ)*x 0 + (2727573929/5000000000 : ℝ)*x 1 + (-18743969/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252194443/10000000000 : ℝ)^5447 ≤ (11311883534011/25000000000000 : ℝ)^4423 := by
    have hnat : (5252194443 : ℕ)^5447*25000000000000^4423 ≤ 11311883534011^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252194443 10000000000 11311883534011 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727573929/5000000000 : ℝ)^5447 ≤ (47410304484017/100000000000000 : ℝ)^4423 := by
    have hnat : (2727573929 : ℕ)^5447*100000000000000^4423 ≤ 47410304484017^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727573929 5000000000 47410304484017 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18743969/156250000 : ℝ)^5447 ≤ (7342161365613/100000000000000 : ℝ)^4423 := by
    have hnat : (18743969 : ℕ)^5447*100000000000000^4423 ≤ 7342161365613^4423*156250000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18743969 156250000 7342161365613 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252194443/10000000000 : ℝ), (2727573929/5000000000 : ℝ), (-18743969/156250000 : ℝ)] ![(11311883534011/25000000000000 : ℝ), (47410304484017/100000000000000 : ℝ), (7342161365613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252194443/10000000000 : ℝ)|^5447 ≤ (11311883534011/25000000000000 : ℝ)^4423
        have hw : |(5252194443/10000000000 : ℝ)|=(5252194443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727573929/5000000000 : ℝ)|^5447 ≤ (47410304484017/100000000000000 : ℝ)^4423
        have hw : |(2727573929/5000000000 : ℝ)|=(2727573929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-18743969/156250000 : ℝ)|^5447 ≤ (7342161365613/100000000000000 : ℝ)^4423
        have hw : |(-18743969/156250000 : ℝ)|=(18743969/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_s3_7 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1020671163/2500000000 : ℝ)*x 0 + (4569393547/10000000000 : ℝ)*x 1 + (3629491493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020671163/2500000000 : ℝ)^5447 ≤ (1327190142759/4000000000000 : ℝ)^4423 := by
    have hnat : (1020671163 : ℕ)^5447*4000000000000^4423 ≤ 1327190142759^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020671163 2500000000 1327190142759 4000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4569393547/10000000000 : ℝ)^5447 ≤ (38116236718641/100000000000000 : ℝ)^4423 := by
    have hnat : (4569393547 : ℕ)^5447*100000000000000^4423 ≤ 38116236718641^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4569393547 10000000000 38116236718641 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3629491493/10000000000 : ℝ)^5447 ≤ (2870400970277/10000000000000 : ℝ)^4423 := by
    have hnat : (3629491493 : ℕ)^5447*10000000000000^4423 ≤ 2870400970277^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629491493 10000000000 2870400970277 10000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020671163/2500000000 : ℝ), (4569393547/10000000000 : ℝ), (3629491493/10000000000 : ℝ)] ![(1327190142759/4000000000000 : ℝ), (38116236718641/100000000000000 : ℝ), (2870400970277/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020671163/2500000000 : ℝ)|^5447 ≤ (1327190142759/4000000000000 : ℝ)^4423
        have hw : |(1020671163/2500000000 : ℝ)|=(1020671163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4569393547/10000000000 : ℝ)|^5447 ≤ (38116236718641/100000000000000 : ℝ)^4423
        have hw : |(4569393547/10000000000 : ℝ)|=(4569393547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3629491493/10000000000 : ℝ)|^5447 ≤ (2870400970277/10000000000000 : ℝ)^4423
        have hw : |(3629491493/10000000000 : ℝ)|=(3629491493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1728_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10141/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16963/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1267/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16969/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1267/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1267/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16969/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1267/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1267/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16969/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1267/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1267/12500 : ℝ) ^ (5439/1024 : ℝ) ≤ (524369177484303/100000000000000000000 : ℝ) := by
    have hpowers : (1267/12500 : ℝ)^5439 ≤ (524369177484303/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1267 : ℕ)^5439*100000000000000000000^1024 ≤ 524369177484303^1024*12500^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1267 12500 524369177484303 100000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1267/12500 : ℝ)) (X := (524369177484303/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16969/100000 : ℝ) ^ (5439/1024 : ℝ) ≤ (4048285374662451/50000000000000000000 : ℝ) := by
    have hpowers : (16969/100000 : ℝ)^5439 ≤ (4048285374662451/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16969 : ℕ)^5439*50000000000000000000^1024 ≤ 4048285374662451^1024*100000^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16969 100000 4048285374662451 50000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16969/100000 : ℝ)) (X := (4048285374662451/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000524369177484303/50000000000000000000 : ℝ) ≤ (10000019744502749/10000000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (50000524369177484303/50000000000000000000 : ℝ)^1024 ≤ (10000019744502749/10000000000000000 : ℝ)^5439 := by
      have hnat : (50000524369177484303 : ℕ)^1024*10000000000000000^5439 ≤ 10000019744502749^5439*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000524369177484303 50000000000000000000 10000019744502749 10000000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000019744502749/10000000000000000 : ℝ)) (X := (50000524369177484303/50000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001724187985361841/20000000000000000000 : ℝ) ≤ (10000162300673293/10000000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (20001724187985361841/20000000000000000000 : ℝ)^1024 ≤ (10000162300673293/10000000000000000 : ℝ)^5439 := by
      have hnat : (20001724187985361841 : ℕ)^1024*10000000000000000^5439 ≤ 10000162300673293^5439*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001724187985361841 20000000000000000000 10000162300673293 10000000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000162300673293/10000000000000000 : ℝ)) (X := (20001724187985361841/20000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25004048285374662451/25000000000000000000 : ℝ) ≤ (10000304856843837/10000000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (25004048285374662451/25000000000000000000 : ℝ)^1024 ≤ (10000304856843837/10000000000000000 : ℝ)^5439 := by
      have hnat : (25004048285374662451 : ℕ)^1024*10000000000000000^5439 ≤ 10000304856843837^5439*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004048285374662451 25000000000000000000 10000304856843837 10000000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000304856843837/10000000000000000 : ℝ)) (X := (25004048285374662451/25000000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(524369177484303/100000000000000000000 : ℝ) ≤ ((68327245015498015949/68330000000000000000 : ℝ)+2*(8909760659/42706250000000 : ℝ)*(1267/12500 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (68327245015498015949/68330000000000000000 : ℝ)+2*(8909760659/42706250000000 : ℝ)*(1267/12500 : ℝ)=(10000019744502749/10000000000000000 : ℝ) by norm_num, show 1+2*(524369177484303/100000000000000000000 : ℝ)=(50000524369177484303/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4048285374662451/50000000000000000000 : ℝ)+(524369177484303/100000000000000000000 : ℝ) ≤ ((68327245015498015949/68330000000000000000 : ℝ)+(8909760659/42706250000000 : ℝ)*((16969/100000 : ℝ)+(1267/12500 : ℝ)))^(5439/1024 : ℝ) := by
    rw [show (68327245015498015949/68330000000000000000 : ℝ)+(8909760659/42706250000000 : ℝ)*((16969/100000 : ℝ)+(1267/12500 : ℝ))=(10000162300673293/10000000000000000 : ℝ) by norm_num, show 1+(4048285374662451/50000000000000000000 : ℝ)+(524369177484303/100000000000000000000 : ℝ)=(20001724187985361841/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4048285374662451/50000000000000000000 : ℝ) ≤ ((68327245015498015949/68330000000000000000 : ℝ)+2*(8909760659/42706250000000 : ℝ)*(16969/100000 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (68327245015498015949/68330000000000000000 : ℝ)+2*(8909760659/42706250000000 : ℝ)*(16969/100000 : ℝ)=(10000304856843837/10000000000000000 : ℝ) by norm_num, show 1+2*(4048285374662451/50000000000000000000 : ℝ)=(25004048285374662451/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (68327245015498015949/68330000000000000000 : ℝ)*(X 1 0+X 2 0)+(8909760659/42706250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (1267/12500 : ℝ)) (hi := (16969/100000 : ℝ)) (c := (68327245015498015949/68330000000000000000 : ℝ)) (alpha := (8909760659/42706250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (68327245015498015949/68330000000000000000 : ℝ)*(X 0 1+X 2 1)+(8909760659/42706250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (1267/12500 : ℝ)) (hi := (16969/100000 : ℝ)) (c := (68327245015498015949/68330000000000000000 : ℝ)) (alpha := (8909760659/42706250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (68327245015498015949/68330000000000000000 : ℝ)*(X 0 2+X 1 2)+(8909760659/42706250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (1267/12500 : ℝ)) (hi := (16969/100000 : ℝ)) (c := (68327245015498015949/68330000000000000000 : ℝ)) (alpha := (8909760659/42706250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-337402097/2500000000 : ℝ)*X 0 0+(341174049/625000000 : ℝ)*X 0 1+(5140189407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5337465041/10000000000 : ℝ)*X 1 0+(-1514572427/10000000000 : ℝ)*X 1 1+(5140189477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1067493013/2000000000 : ℝ)*X 2 0+(25700947/50000000 : ℝ)*X 2 1+(-757286249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1020564527/2500000000 : ℝ)*X 0 0+(3618512189/10000000000 : ℝ)*X 0 1+(4580211763/10000000000 : ℝ)*X 0 2+(1020564527/2500000000 : ℝ)*X 1 0+(3618512189/10000000000 : ℝ)*X 1 1+(4580211763/10000000000 : ℝ)*X 1 2+(1020564527/2500000000 : ℝ)*X 2 0+(3618512189/10000000000 : ℝ)*X 2 1+(4580211763/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-674874883/5000000000 : ℝ)*X 0 0+(1028754681/2000000000 : ℝ)*X 0 1+(5455147471/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252194707/10000000000 : ℝ)*X 1 0+(-599806953/5000000000 : ℝ)*X 1 1+(2727573837/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5252194443/10000000000 : ℝ)*X 2 0+(2727573929/5000000000 : ℝ)*X 2 1+(-18743969/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1020671163/2500000000 : ℝ)*X 0 0+(4569393547/10000000000 : ℝ)*X 0 1+(3629491493/10000000000 : ℝ)*X 0 2+(1020671163/2500000000 : ℝ)*X 1 0+(4569393547/10000000000 : ℝ)*X 1 1+(3629491493/10000000000 : ℝ)*X 1 2+(1020671163/2500000000 : ℝ)*X 2 0+(4569393547/10000000000 : ℝ)*X 2 1+(3629491493/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (398892954954571424178297/34165000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47840959/3125000000000 : ℝ)*(base19) + (1434481009/100000000000000 : ℝ)*(base23) + (2950107/5000000000000 : ℝ)*(lower2) + (154306103/50000000000000 : ℝ)*(upper3) + (185836559/100000000000000 : ℝ)*(upper5) + (1044661110451957/50000000000000 : ℝ)*(major0) + (1044661110451957/50000000000000 : ℝ)*(major1) + (1044661110451957/50000000000000 : ℝ)*(major2) + (49043645517829/1562500000000 : ℝ)*(sp0) + (3138806303307551/100000000000000 : ℝ)*(sp1) + (313880639973723/10000000000000 : ℝ)*(sp2) + (1039830482650699/100000000000000 : ℝ)*(sp3) + (14521077183/100000000000000 : ℝ)*(sp4) + (143393901/2500000000000 : ℝ)*(sp7) + (1039836218406739/100000000000000 : ℝ)*(f.failure) + (2452193620483/78125000000 : ℝ)*(f.sum) + (8404572467663/17082500000000000000000000000 : ℝ)*base65 + (5927650339519937807/3416500000000000000000000000000000 : ℝ)*base68 + (7565700140152062193/3416500000000000000000000000000000 : ℝ)*base69 + (2508418768755562193/3416500000000000000000000000000000 : ℝ)*base71 + (98116756519797/17082500000000000000000000000 : ℝ)*base74 + (2542332304540937807/3416500000000000000000000000000000 : ℝ)*base76 + (22423042299732062193/3416500000000000000000000000000000 : ℝ)*base77 + (15579782082606437807/3416500000000000000000000000000000 : ℝ)*base80 + (109851002010911/34165000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3785939/1000000000000000000000 : ℝ)*base89 + (3785939/1000000000000000000000 : ℝ)*base91 + (3785939/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (141279937136622357243003/34165000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65205309/10000000000000 : ℝ)*(base19) + (122940479/25000000000000 : ℝ)*(base23) + (241146477/100000000000000 : ℝ)*(lower1) + (56824659/50000000000000 : ℝ)*(upper3) + (242393/10000000000000 : ℝ)*(lower4) + (11832967/25000000000000 : ℝ)*(upper5) + (534437502832679/25000000000000 : ℝ)*(major0) + (534437502832679/25000000000000 : ℝ)*(major1) + (534437502832679/25000000000000 : ℝ)*(major2) + (42846357/20000000000000 : ℝ)*(sp1) + (160578080298303/5000000000000 : ℝ)*(sp4) + (1605780369840593/50000000000000 : ℝ)*(sp5) + (200722569637759/6250000000000 : ℝ)*(sp6) + (1063938278854559/100000000000000 : ℝ)*(sp7) + (1063938278854559/100000000000000 : ℝ)*(f.failure) + (160578080298303/5000000000000 : ℝ)*(f.sum) + (26278310895921/8541250000000000000000000000 : ℝ)*base65 + (2516612653394252629/1708250000000000000000000000000000 : ℝ)*base68 + (8515546385670247371/1708250000000000000000000000000000 : ℝ)*base69 + (2865444071029247371/1708250000000000000000000000000000 : ℝ)*base71 + (61646374439363/17082500000000000000000000000 : ℝ)*base74 + (4269942214409002629/1708250000000000000000000000000000 : ℝ)*base76 + (2183577113412997371/1708250000000000000000000000000000 : ℝ)*base77 + (3807518818123252629/1708250000000000000000000000000000 : ℝ)*base80 + (263416847100809/34165000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1929759/1000000000000000000000 : ℝ)*base89 + (1929759/1000000000000000000000 : ℝ)*base91 + (1929759/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1728_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10141/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16963/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1728_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1728_box_0 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-208863757/2000000000 : ℝ)*x 0 + (5407898677/10000000000 : ℝ)*x 1 + (5407898601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208863757/2000000000 : ℝ)^5447 ≤ (96715532667/1562500000000 : ℝ)^4423 := by
    have hnat : (208863757 : ℕ)^5447*1562500000000^4423 ≤ 96715532667^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208863757 2000000000 96715532667 1562500000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407898677/10000000000 : ℝ)^5447 ≤ (46905103354251/100000000000000 : ℝ)^4423 := by
    have hnat : (5407898677 : ℕ)^5447*100000000000000^4423 ≤ 46905103354251^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407898677 10000000000 46905103354251 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407898601/10000000000 : ℝ)^5447 ≤ (46905102542457/100000000000000 : ℝ)^4423 := by
    have hnat : (5407898601 : ℕ)^5447*100000000000000^4423 ≤ 46905102542457^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407898601 10000000000 46905102542457 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208863757/2000000000 : ℝ), (5407898677/10000000000 : ℝ), (5407898601/10000000000 : ℝ)] ![(96715532667/1562500000000 : ℝ), (46905103354251/100000000000000 : ℝ), (46905102542457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208863757/2000000000 : ℝ)|^5447 ≤ (96715532667/1562500000000 : ℝ)^4423
        have hw : |(-208863757/2000000000 : ℝ)|=(208863757/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407898677/10000000000 : ℝ)|^5447 ≤ (46905103354251/100000000000000 : ℝ)^4423
        have hw : |(5407898677/10000000000 : ℝ)|=(5407898677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407898601/10000000000 : ℝ)|^5447 ≤ (46905102542457/100000000000000 : ℝ)^4423
        have hw : |(5407898601/10000000000 : ℝ)|=(5407898601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_1 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5224317731/10000000000 : ℝ)*x 0 + (-326202389/2500000000 : ℝ)*x 1 + (5407898591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5224317731/10000000000 : ℝ)^5447 ≤ (44951958368011/100000000000000 : ℝ)^4423 := by
    have hnat : (5224317731 : ℕ)^5447*100000000000000^4423 ≤ 44951958368011^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224317731 10000000000 44951958368011 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326202389/2500000000 : ℝ)^5447 ≤ (8142939188177/100000000000000 : ℝ)^4423 := by
    have hnat : (326202389 : ℕ)^5447*100000000000000^4423 ≤ 8142939188177^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326202389 2500000000 8142939188177 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407898591/10000000000 : ℝ)^5447 ≤ (23452551217821/50000000000000 : ℝ)^4423 := by
    have hnat : (5407898591 : ℕ)^5447*50000000000000^4423 ≤ 23452551217821^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407898591 10000000000 23452551217821 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5224317731/10000000000 : ℝ), (-326202389/2500000000 : ℝ), (5407898591/10000000000 : ℝ)] ![(44951958368011/100000000000000 : ℝ), (8142939188177/100000000000000 : ℝ), (23452551217821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5224317731/10000000000 : ℝ)|^5447 ≤ (44951958368011/100000000000000 : ℝ)^4423
        have hw : |(5224317731/10000000000 : ℝ)|=(5224317731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-326202389/2500000000 : ℝ)|^5447 ≤ (8142939188177/100000000000000 : ℝ)^4423
        have hw : |(-326202389/2500000000 : ℝ)|=(326202389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407898591/10000000000 : ℝ)|^5447 ≤ (23452551217821/50000000000000 : ℝ)^4423
        have hw : |(5407898591/10000000000 : ℝ)|=(5407898591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_2 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1306079403/2500000000 : ℝ)*x 0 + (1351974687/2500000000 : ℝ)*x 1 + (-1304809501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1306079403/2500000000 : ℝ)^5447 ≤ (11237989276759/25000000000000 : ℝ)^4423 := by
    have hnat : (1306079403 : ℕ)^5447*25000000000000^4423 ≤ 11237989276759^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306079403 2500000000 11237989276759 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351974687/2500000000 : ℝ)^5447 ≤ (46905104112637/100000000000000 : ℝ)^4423 := by
    have hnat : (1351974687 : ℕ)^5447*100000000000000^4423 ≤ 46905104112637^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351974687 2500000000 46905104112637 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304809501/10000000000 : ℝ)^5447 ≤ (254466836421/3125000000000 : ℝ)^4423 := by
    have hnat : (1304809501 : ℕ)^5447*3125000000000^4423 ≤ 254466836421^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304809501 10000000000 254466836421 3125000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1306079403/2500000000 : ℝ), (1351974687/2500000000 : ℝ), (-1304809501/10000000000 : ℝ)] ![(11237989276759/25000000000000 : ℝ), (46905104112637/100000000000000 : ℝ), (254466836421/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1306079403/2500000000 : ℝ)|^5447 ≤ (11237989276759/25000000000000 : ℝ)^4423
        have hw : |(1306079403/2500000000 : ℝ)|=(1306079403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351974687/2500000000 : ℝ)|^5447 ≤ (46905104112637/100000000000000 : ℝ)^4423
        have hw : |(1351974687/2500000000 : ℝ)|=(1351974687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1304809501/10000000000 : ℝ)|^5447 ≤ (254466836421/3125000000000 : ℝ)^4423
        have hw : |(-1304809501/10000000000 : ℝ)|=(1304809501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_3 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4462392591/10000000000 : ℝ)*x 0 + (3913025973/10000000000 : ℝ)*x 1 + (3913025983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4462392591/10000000000 : ℝ)^5447 ≤ (37020027253357/100000000000000 : ℝ)^4423 := by
    have hnat : (4462392591 : ℕ)^5447*100000000000000^4423 ≤ 37020027253357^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4462392591 10000000000 37020027253357 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3913025973/10000000000 : ℝ)^5447 ≤ (31489986318499/100000000000000 : ℝ)^4423 := by
    have hnat : (3913025973 : ℕ)^5447*100000000000000^4423 ≤ 31489986318499^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3913025973 10000000000 31489986318499 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3913025983/10000000000 : ℝ)^5447 ≤ (6297997283521/20000000000000 : ℝ)^4423 := by
    have hnat : (3913025983 : ℕ)^5447*20000000000000^4423 ≤ 6297997283521^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3913025983 10000000000 6297997283521 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4462392591/10000000000 : ℝ), (3913025973/10000000000 : ℝ), (3913025983/10000000000 : ℝ)] ![(37020027253357/100000000000000 : ℝ), (31489986318499/100000000000000 : ℝ), (6297997283521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4462392591/10000000000 : ℝ)|^5447 ≤ (37020027253357/100000000000000 : ℝ)^4423
        have hw : |(4462392591/10000000000 : ℝ)|=(4462392591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3913025973/10000000000 : ℝ)|^5447 ≤ (31489986318499/100000000000000 : ℝ)^4423
        have hw : |(3913025973/10000000000 : ℝ)|=(3913025973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3913025983/10000000000 : ℝ)|^5447 ≤ (6297997283521/20000000000000 : ℝ)^4423
        have hw : |(3913025983/10000000000 : ℝ)|=(3913025983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_4 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1675243701/10000000000 : ℝ)*x 0 + (1294491161/2500000000 : ℝ)*x 1 + (1035592959/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1675243701/10000000000 : ℝ)^5447 ≤ (11077424642327/100000000000000 : ℝ)^4423 := by
    have hnat : (1675243701 : ℕ)^5447*100000000000000^4423 ≤ 11077424642327^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1675243701 10000000000 11077424642327 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1294491161/2500000000 : ℝ)^5447 ≤ (44461286869163/100000000000000 : ℝ)^4423 := by
    have hnat : (1294491161 : ℕ)^5447*100000000000000^4423 ≤ 44461286869163^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294491161 2500000000 44461286869163 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035592959/2000000000 : ℝ)^5447 ≤ (22230644232963/50000000000000 : ℝ)^4423 := by
    have hnat : (1035592959 : ℕ)^5447*50000000000000^4423 ≤ 22230644232963^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035592959 2000000000 22230644232963 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1675243701/10000000000 : ℝ), (1294491161/2500000000 : ℝ), (1035592959/2000000000 : ℝ)] ![(11077424642327/100000000000000 : ℝ), (44461286869163/100000000000000 : ℝ), (22230644232963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1675243701/10000000000 : ℝ)|^5447 ≤ (11077424642327/100000000000000 : ℝ)^4423
        have hw : |(-1675243701/10000000000 : ℝ)|=(1675243701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1294491161/2500000000 : ℝ)|^5447 ≤ (44461286869163/100000000000000 : ℝ)^4423
        have hw : |(1294491161/2500000000 : ℝ)|=(1294491161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1035592959/2000000000 : ℝ)|^5447 ≤ (22230644232963/50000000000000 : ℝ)^4423
        have hw : |(1035592959/2000000000 : ℝ)|=(1035592959/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_5 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379595269/10000000000 : ℝ)*x 0 + (-703527027/5000000000 : ℝ)*x 1 + (1294491537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379595269/10000000000 : ℝ)^5447 ≤ (46602964088597/100000000000000 : ℝ)^4423 := by
    have hnat : (5379595269 : ℕ)^5447*100000000000000^4423 ≤ 46602964088597^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379595269 10000000000 46602964088597 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (703527027/5000000000 : ℝ)^5447 ≤ (17871466247/200000000000 : ℝ)^4423 := by
    have hnat : (703527027 : ℕ)^5447*200000000000^4423 ≤ 17871466247^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703527027 5000000000 17871466247 200000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294491537/2500000000 : ℝ)^5447 ≤ (22230651386671/50000000000000 : ℝ)^4423 := by
    have hnat : (1294491537 : ℕ)^5447*50000000000000^4423 ≤ 22230651386671^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294491537 2500000000 22230651386671 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379595269/10000000000 : ℝ), (-703527027/5000000000 : ℝ), (1294491537/2500000000 : ℝ)] ![(46602964088597/100000000000000 : ℝ), (17871466247/200000000000 : ℝ), (22230651386671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379595269/10000000000 : ℝ)|^5447 ≤ (46602964088597/100000000000000 : ℝ)^4423
        have hw : |(5379595269/10000000000 : ℝ)|=(5379595269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-703527027/5000000000 : ℝ)|^5447 ≤ (17871466247/200000000000 : ℝ)^4423
        have hw : |(-703527027/5000000000 : ℝ)|=(703527027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294491537/2500000000 : ℝ)|^5447 ≤ (22230651386671/50000000000000 : ℝ)^4423
        have hw : |(1294491537/2500000000 : ℝ)|=(1294491537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_6 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689797637/5000000000 : ℝ)*x 0 + (2022643/3906250 : ℝ)*x 1 + (-70352707/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689797637/5000000000 : ℝ)^5447 ≤ (2330148207097/5000000000000 : ℝ)^4423 := by
    have hnat : (2689797637 : ℕ)^5447*5000000000000^4423 ≤ 2330148207097^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689797637 5000000000 2330148207097 5000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022643/3906250 : ℝ)^5447 ≤ (4446130205427/10000000000000 : ℝ)^4423 := by
    have hnat : (2022643 : ℕ)^5447*10000000000000^4423 ≤ 4446130205427^4423*3906250^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022643 3906250 4446130205427 10000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70352707/500000000 : ℝ)^5447 ≤ (8935733796103/100000000000000 : ℝ)^4423 := by
    have hnat : (70352707 : ℕ)^5447*100000000000000^4423 ≤ 8935733796103^4423*500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70352707 500000000 8935733796103 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689797637/5000000000 : ℝ), (2022643/3906250 : ℝ), (-70352707/500000000 : ℝ)] ![(2330148207097/5000000000000 : ℝ), (4446130205427/10000000000000 : ℝ), (8935733796103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689797637/5000000000 : ℝ)|^5447 ≤ (2330148207097/5000000000000 : ℝ)^4423
        have hw : |(2689797637/5000000000 : ℝ)|=(2689797637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2022643/3906250 : ℝ)|^5447 ≤ (4446130205427/10000000000000 : ℝ)^4423
        have hw : |(2022643/3906250 : ℝ)|=(2022643/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70352707/500000000 : ℝ)|^5447 ≤ (8935733796103/100000000000000 : ℝ)^4423
        have hw : |(-70352707/500000000 : ℝ)|=(70352707/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_7 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (368556071/1000000000 : ℝ)*x 0 + (1075160311/2500000000 : ℝ)*x 1 + (430064101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (368556071/1000000000 : ℝ)^5447 ≤ (7312767313611/25000000000000 : ℝ)^4423 := by
    have hnat : (368556071 : ℕ)^5447*25000000000000^4423 ≤ 7312767313611^4423*1000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368556071 1000000000 7312767313611 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075160311/2500000000 : ℝ)^5447 ≤ (17687233277281/50000000000000 : ℝ)^4423 := by
    have hnat : (1075160311 : ℕ)^5447*50000000000000^4423 ≤ 17687233277281^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075160311 2500000000 17687233277281 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430064101/1000000000 : ℝ)^5447 ≤ (35374464184209/100000000000000 : ℝ)^4423 := by
    have hnat : (430064101 : ℕ)^5447*100000000000000^4423 ≤ 35374464184209^4423*1000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430064101 1000000000 35374464184209 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(368556071/1000000000 : ℝ), (1075160311/2500000000 : ℝ), (430064101/1000000000 : ℝ)] ![(7312767313611/25000000000000 : ℝ), (17687233277281/50000000000000 : ℝ), (35374464184209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(368556071/1000000000 : ℝ)|^5447 ≤ (7312767313611/25000000000000 : ℝ)^4423
        have hw : |(368556071/1000000000 : ℝ)|=(368556071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075160311/2500000000 : ℝ)|^5447 ≤ (17687233277281/50000000000000 : ℝ)^4423
        have hw : |(1075160311/2500000000 : ℝ)|=(1075160311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(430064101/1000000000 : ℝ)|^5447 ≤ (35374464184209/100000000000000 : ℝ)^4423
        have hw : |(430064101/1000000000 : ℝ)|=(430064101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_8 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-307864943/2000000000 : ℝ)*x 0 + (156481329/312500000 : ℝ)*x 1 + (27249521/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (307864943/2000000000 : ℝ)^5447 ≤ (4990606473837/50000000000000 : ℝ)^4423 := by
    have hnat : (307864943 : ℕ)^5447*50000000000000^4423 ≤ 4990606473837^4423*2000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307864943 2000000000 4990606473837 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156481329/312500000 : ℝ)^5447 ≤ (42664599325613/100000000000000 : ℝ)^4423 := by
    have hnat : (156481329 : ℕ)^5447*100000000000000^4423 ≤ 42664599325613^4423*312500000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156481329 312500000 42664599325613 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27249521/50000000 : ℝ)^5447 ≤ (2959636732061/6250000000000 : ℝ)^4423 := by
    have hnat : (27249521 : ℕ)^5447*6250000000000^4423 ≤ 2959636732061^4423*50000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27249521 50000000 2959636732061 6250000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-307864943/2000000000 : ℝ), (156481329/312500000 : ℝ), (27249521/50000000 : ℝ)] ![(4990606473837/50000000000000 : ℝ), (42664599325613/100000000000000 : ℝ), (2959636732061/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-307864943/2000000000 : ℝ)|^5447 ≤ (4990606473837/50000000000000 : ℝ)^4423
        have hw : |(-307864943/2000000000 : ℝ)|=(307864943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156481329/312500000 : ℝ)|^5447 ≤ (42664599325613/100000000000000 : ℝ)^4423
        have hw : |(156481329/312500000 : ℝ)|=(156481329/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27249521/50000000 : ℝ)|^5447 ≤ (2959636732061/6250000000000 : ℝ)^4423
        have hw : |(27249521/50000000 : ℝ)|=(27249521/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_9 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597987691/5000000000 : ℝ)*x 0 + (-1285395597/10000000000 : ℝ)*x 1 + (5449904417/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597987691/5000000000 : ℝ)^5447 ≤ (22325909795049/50000000000000 : ℝ)^4423 := by
    have hnat : (2597987691 : ℕ)^5447*50000000000000^4423 ≤ 22325909795049^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597987691 5000000000 22325909795049 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285395597/10000000000 : ℝ)^5447 ≤ (7993990362879/100000000000000 : ℝ)^4423 := by
    have hnat : (1285395597 : ℕ)^5447*100000000000000^4423 ≤ 7993990362879^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285395597 10000000000 7993990362879 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5449904417/10000000000 : ℝ)^5447 ≤ (5919273754377/12500000000000 : ℝ)^4423 := by
    have hnat : (5449904417 : ℕ)^5447*12500000000000^4423 ≤ 5919273754377^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5449904417 10000000000 5919273754377 12500000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597987691/5000000000 : ℝ), (-1285395597/10000000000 : ℝ), (5449904417/10000000000 : ℝ)] ![(22325909795049/50000000000000 : ℝ), (7993990362879/100000000000000 : ℝ), (5919273754377/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597987691/5000000000 : ℝ)|^5447 ≤ (22325909795049/50000000000000 : ℝ)^4423
        have hw : |(2597987691/5000000000 : ℝ)|=(2597987691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1285395597/10000000000 : ℝ)|^5447 ≤ (7993990362879/100000000000000 : ℝ)^4423
        have hw : |(-1285395597/10000000000 : ℝ)|=(1285395597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5449904417/10000000000 : ℝ)|^5447 ≤ (5919273754377/12500000000000 : ℝ)^4423
        have hw : |(5449904417/10000000000 : ℝ)|=(5449904417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_10 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597987599/5000000000 : ℝ)*x 0 + (2724952211/5000000000 : ℝ)*x 1 + (-321348961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597987599/5000000000 : ℝ)^5447 ≤ (44651817642809/100000000000000 : ℝ)^4423 := by
    have hnat : (2597987599 : ℕ)^5447*100000000000000^4423 ≤ 44651817642809^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597987599 5000000000 44651817642809 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2724952211/5000000000 : ℝ)^5447 ≤ (47354190088519/100000000000000 : ℝ)^4423 := by
    have hnat : (2724952211 : ℕ)^5447*100000000000000^4423 ≤ 47354190088519^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2724952211 5000000000 47354190088519 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (321348961/2500000000 : ℝ)^5447 ≤ (7993992254631/100000000000000 : ℝ)^4423 := by
    have hnat : (321348961 : ℕ)^5447*100000000000000^4423 ≤ 7993992254631^4423*2500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321348961 2500000000 7993992254631 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597987599/5000000000 : ℝ), (2724952211/5000000000 : ℝ), (-321348961/2500000000 : ℝ)] ![(44651817642809/100000000000000 : ℝ), (47354190088519/100000000000000 : ℝ), (7993992254631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597987599/5000000000 : ℝ)|^5447 ≤ (44651817642809/100000000000000 : ℝ)^4423
        have hw : |(2597987599/5000000000 : ℝ)|=(2597987599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2724952211/5000000000 : ℝ)|^5447 ≤ (47354190088519/100000000000000 : ℝ)^4423
        have hw : |(2724952211/5000000000 : ℝ)|=(2724952211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-321348961/2500000000 : ℝ)|^5447 ≤ (7993992254631/100000000000000 : ℝ)^4423
        have hw : |(-321348961/2500000000 : ℝ)|=(321348961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_11 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2299681049/5000000000 : ℝ)*x 0 + (3842027777/10000000000 : ℝ)*x 1 + (3842027249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2299681049/5000000000 : ℝ)^5447 ≤ (19212166577393/50000000000000 : ℝ)^4423 := by
    have hnat : (2299681049 : ℕ)^5447*50000000000000^4423 ≤ 19212166577393^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299681049 5000000000 19212166577393 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3842027777/10000000000 : ℝ)^5447 ≤ (15393918008189/50000000000000 : ℝ)^4423 := by
    have hnat : (3842027777 : ℕ)^5447*50000000000000^4423 ≤ 15393918008189^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3842027777 10000000000 15393918008189 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3842027249/10000000000 : ℝ)^5447 ≤ (6157566161143/20000000000000 : ℝ)^4423 := by
    have hnat : (3842027249 : ℕ)^5447*20000000000000^4423 ≤ 6157566161143^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3842027249 10000000000 6157566161143 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2299681049/5000000000 : ℝ), (3842027777/10000000000 : ℝ), (3842027249/10000000000 : ℝ)] ![(19212166577393/50000000000000 : ℝ), (15393918008189/50000000000000 : ℝ), (6157566161143/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2299681049/5000000000 : ℝ)|^5447 ≤ (19212166577393/50000000000000 : ℝ)^4423
        have hw : |(2299681049/5000000000 : ℝ)|=(2299681049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3842027777/10000000000 : ℝ)|^5447 ≤ (15393918008189/50000000000000 : ℝ)^4423
        have hw : |(3842027777/10000000000 : ℝ)|=(3842027777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3842027249/10000000000 : ℝ)|^5447 ≤ (6157566161143/20000000000000 : ℝ)^4423
        have hw : |(3842027249/10000000000 : ℝ)|=(3842027249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_12 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-146788463/1250000000 : ℝ)*x 0 + (2785351401/5000000000 : ℝ)*x 1 + (5153053241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (146788463/1250000000 : ℝ)^5447 ≤ (893985668267/12500000000000 : ℝ)^4423 := by
    have hnat : (146788463 : ℕ)^5447*12500000000000^4423 ≤ 893985668267^4423*1250000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146788463 1250000000 893985668267 12500000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785351401/5000000000 : ℝ)^5447 ≤ (12162527166357/25000000000000 : ℝ)^4423 := by
    have hnat : (2785351401 : ℕ)^5447*25000000000000^4423 ≤ 12162527166357^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785351401 5000000000 12162527166357 25000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153053241/10000000000 : ℝ)^5447 ≤ (44198005978687/100000000000000 : ℝ)^4423 := by
    have hnat : (5153053241 : ℕ)^5447*100000000000000^4423 ≤ 44198005978687^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153053241 10000000000 44198005978687 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-146788463/1250000000 : ℝ), (2785351401/5000000000 : ℝ), (5153053241/10000000000 : ℝ)] ![(893985668267/12500000000000 : ℝ), (12162527166357/25000000000000 : ℝ), (44198005978687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-146788463/1250000000 : ℝ)|^5447 ≤ (893985668267/12500000000000 : ℝ)^4423
        have hw : |(-146788463/1250000000 : ℝ)|=(146788463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785351401/5000000000 : ℝ)|^5447 ≤ (12162527166357/25000000000000 : ℝ)^4423
        have hw : |(2785351401/5000000000 : ℝ)|=(2785351401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153053241/10000000000 : ℝ)|^5447 ≤ (44198005978687/100000000000000 : ℝ)^4423
        have hw : |(5153053241/10000000000 : ℝ)|=(5153053241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_13 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396452599/10000000000 : ℝ)*x 0 + (-708853417/5000000000 : ℝ)*x 1 + (5153053333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396452599/10000000000 : ℝ)^5447 ≤ (4678287211593/10000000000000 : ℝ)^4423 := by
    have hnat : (5396452599 : ℕ)^5447*10000000000000^4423 ≤ 4678287211593^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396452599 10000000000 4678287211593 10000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708853417/5000000000 : ℝ)^5447 ≤ (4509560461951/50000000000000 : ℝ)^4423 := by
    have hnat : (708853417 : ℕ)^5447*50000000000000^4423 ≤ 4509560461951^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708853417 5000000000 4509560461951 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5153053333/10000000000 : ℝ)^5447 ≤ (690593858601/1562500000000 : ℝ)^4423 := by
    have hnat : (5153053333 : ℕ)^5447*1562500000000^4423 ≤ 690593858601^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5153053333 10000000000 690593858601 1562500000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396452599/10000000000 : ℝ), (-708853417/5000000000 : ℝ), (5153053333/10000000000 : ℝ)] ![(4678287211593/10000000000000 : ℝ), (4509560461951/50000000000000 : ℝ), (690593858601/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396452599/10000000000 : ℝ)|^5447 ≤ (4678287211593/10000000000000 : ℝ)^4423
        have hw : |(5396452599/10000000000 : ℝ)|=(5396452599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-708853417/5000000000 : ℝ)|^5447 ≤ (4509560461951/50000000000000 : ℝ)^4423
        have hw : |(-708853417/5000000000 : ℝ)|=(708853417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5153053333/10000000000 : ℝ)|^5447 ≤ (690593858601/1562500000000 : ℝ)^4423
        have hw : |(5153053333/10000000000 : ℝ)|=(5153053333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_14 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (269822633/500000000 : ℝ)*x 0 + (2576526651/5000000000 : ℝ)*x 1 + (-177213349/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269822633/500000000 : ℝ)^5447 ≤ (46782872767181/100000000000000 : ℝ)^4423 := by
    have hnat : (269822633 : ℕ)^5447*100000000000000^4423 ≤ 46782872767181^4423*500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269822633 500000000 46782872767181 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576526651/5000000000 : ℝ)^5447 ≤ (44198006623017/100000000000000 : ℝ)^4423 := by
    have hnat : (2576526651 : ℕ)^5447*100000000000000^4423 ≤ 44198006623017^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576526651 5000000000 44198006623017 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177213349/1250000000 : ℝ)^5447 ≤ (281847518589/3125000000000 : ℝ)^4423 := by
    have hnat : (177213349 : ℕ)^5447*3125000000000^4423 ≤ 281847518589^4423*1250000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177213349 1250000000 281847518589 3125000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269822633/500000000 : ℝ), (2576526651/5000000000 : ℝ), (-177213349/1250000000 : ℝ)] ![(46782872767181/100000000000000 : ℝ), (44198006623017/100000000000000 : ℝ), (281847518589/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269822633/500000000 : ℝ)|^5447 ≤ (46782872767181/100000000000000 : ℝ)^4423
        have hw : |(269822633/500000000 : ℝ)|=(269822633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576526651/5000000000 : ℝ)|^5447 ≤ (44198006623017/100000000000000 : ℝ)^4423
        have hw : |(2576526651/5000000000 : ℝ)|=(2576526651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-177213349/1250000000 : ℝ)|^5447 ≤ (281847518589/3125000000000 : ℝ)^4423
        have hw : |(-177213349/1250000000 : ℝ)|=(177213349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1728_box_15 (p : ℝ) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1799206979/5000000000 : ℝ)*x 0 + (4342522017/10000000000 : ℝ)*x 1 + (217126111/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1799206979/5000000000 : ℝ)^5447 ≤ (28401630332643/100000000000000 : ℝ)^4423 := by
    have hnat : (1799206979 : ℕ)^5447*100000000000000^4423 ≤ 28401630332643^4423*5000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799206979 5000000000 28401630332643 100000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4342522017/10000000000 : ℝ)^5447 ≤ (7159836759439/20000000000000 : ℝ)^4423 := by
    have hnat : (4342522017 : ℕ)^5447*20000000000000^4423 ≤ 7159836759439^4423*10000000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342522017 10000000000 7159836759439 20000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217126111/500000000 : ℝ)^5447 ≤ (17899592929073/50000000000000 : ℝ)^4423 := by
    have hnat : (217126111 : ℕ)^5447*50000000000000^4423 ≤ 17899592929073^4423*500000000^5447 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217126111 500000000 17899592929073 50000000000000 5447 4423 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5447/1024 : ℝ)) 5447 4423 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1799206979/5000000000 : ℝ), (4342522017/10000000000 : ℝ), (217126111/500000000 : ℝ)] ![(28401630332643/100000000000000 : ℝ), (7159836759439/20000000000000 : ℝ), (17899592929073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1799206979/5000000000 : ℝ)|^5447 ≤ (28401630332643/100000000000000 : ℝ)^4423
        have hw : |(1799206979/5000000000 : ℝ)|=(1799206979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4342522017/10000000000 : ℝ)|^5447 ≤ (7159836759439/20000000000000 : ℝ)^4423
        have hw : |(4342522017/10000000000 : ℝ)|=(4342522017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217126111/500000000 : ℝ)|^5447 ≤ (17899592929073/50000000000000 : ℝ)^4423
        have hw : |(217126111/500000000 : ℝ)|=(217126111/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1728_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66923/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29411/50000 : ℝ) ∧ (41023/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (45337/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16963/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10141/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16963/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10141/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16963/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10141/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10141/100000 : ℝ) ^ (5439/1024 : ℝ) ≤ (131436138419677/25000000000000000000 : ℝ) := by
    have hpowers : (10141/100000 : ℝ)^5439 ≤ (131436138419677/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10141 : ℕ)^5439*25000000000000000000^1024 ≤ 131436138419677^1024*100000^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10141 100000 131436138419677 25000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10141/100000 : ℝ)) (X := (131436138419677/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16963/100000 : ℝ) ^ (5439/1024 : ℝ) ≤ (404068816370837/5000000000000000000 : ℝ) := by
    have hpowers : (16963/100000 : ℝ)^5439 ≤ (404068816370837/5000000000000000000 : ℝ)^1024 := by
      have hnat : (16963 : ℕ)^5439*5000000000000000000^1024 ≤ 404068816370837^1024*100000^5439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16963 100000 404068816370837 5000000000000000000 5439 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16963/100000 : ℝ)) (X := (404068816370837/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500131436138419677/12500000000000000000 : ℝ) ≤ (1250002474536337/1250000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (12500131436138419677/12500000000000000000 : ℝ)^1024 ≤ (1250002474536337/1250000000000000 : ℝ)^5439 := by
      have hnat : (12500131436138419677 : ℕ)^1024*1250000000000000^5439 ≤ 1250002474536337^5439*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500131436138419677 12500000000000000000 1250002474536337 1250000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250002474536337/1250000000000000 : ℝ)) (X := (12500131436138419677/12500000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12501075890110136931/12500000000000000000 : ℝ) ≤ (2500040510130111/2500000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (12501075890110136931/12500000000000000000 : ℝ)^1024 ≤ (2500040510130111/2500000000000000 : ℝ)^5439 := by
      have hnat : (12501075890110136931 : ℕ)^1024*2500000000000000^5439 ≤ 2500040510130111^5439*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501075890110136931 12500000000000000000 2500040510130111 2500000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500040510130111/2500000000000000 : ℝ)) (X := (12501075890110136931/12500000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2500404068816370837/2500000000000000000 : ℝ) ≤ (625019017796887/625000000000000 : ℝ) ^ (5439/1024 : ℝ) := by
    have hpowers : (2500404068816370837/2500000000000000000 : ℝ)^1024 ≤ (625019017796887/625000000000000 : ℝ)^5439 := by
      have hnat : (2500404068816370837 : ℕ)^1024*625000000000000^5439 ≤ 625019017796887^5439*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500404068816370837 2500000000000000000 625019017796887 625000000000000 1024 5439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625019017796887/625000000000000 : ℝ)) (X := (2500404068816370837/2500000000000000000 : ℝ)) (by norm_num) 5439 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(131436138419677/25000000000000000000 : ℝ) ≤ ((8527156256603422397/8527500000000000000 : ℝ)+2*(35561057437/170550000000000 : ℝ)*(10141/100000 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (8527156256603422397/8527500000000000000 : ℝ)+2*(35561057437/170550000000000 : ℝ)*(10141/100000 : ℝ)=(1250002474536337/1250000000000000 : ℝ) by norm_num, show 1+2*(131436138419677/25000000000000000000 : ℝ)=(12500131436138419677/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(404068816370837/5000000000000000000 : ℝ)+(131436138419677/25000000000000000000 : ℝ) ≤ ((8527156256603422397/8527500000000000000 : ℝ)+(35561057437/170550000000000 : ℝ)*((16963/100000 : ℝ)+(10141/100000 : ℝ)))^(5439/1024 : ℝ) := by
    rw [show (8527156256603422397/8527500000000000000 : ℝ)+(35561057437/170550000000000 : ℝ)*((16963/100000 : ℝ)+(10141/100000 : ℝ))=(2500040510130111/2500000000000000 : ℝ) by norm_num, show 1+(404068816370837/5000000000000000000 : ℝ)+(131436138419677/25000000000000000000 : ℝ)=(12501075890110136931/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(404068816370837/5000000000000000000 : ℝ) ≤ ((8527156256603422397/8527500000000000000 : ℝ)+2*(35561057437/170550000000000 : ℝ)*(16963/100000 : ℝ))^(5439/1024 : ℝ) := by
    rw [show (8527156256603422397/8527500000000000000 : ℝ)+2*(35561057437/170550000000000 : ℝ)*(16963/100000 : ℝ)=(625019017796887/625000000000000 : ℝ) by norm_num, show 1+2*(404068816370837/5000000000000000000 : ℝ)=(2500404068816370837/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8527156256603422397/8527500000000000000 : ℝ)*(X 1 0+X 2 0)+(35561057437/170550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (10141/100000 : ℝ)) (hi := (16963/100000 : ℝ)) (c := (8527156256603422397/8527500000000000000 : ℝ)) (alpha := (35561057437/170550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8527156256603422397/8527500000000000000 : ℝ)*(X 0 1+X 2 1)+(35561057437/170550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (10141/100000 : ℝ)) (hi := (16963/100000 : ℝ)) (c := (8527156256603422397/8527500000000000000 : ℝ)) (alpha := (35561057437/170550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8527156256603422397/8527500000000000000 : ℝ)*(X 0 2+X 1 2)+(35561057437/170550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5439/1024 : ℝ)) (lo := (10141/100000 : ℝ)) (hi := (16963/100000 : ℝ)) (c := (8527156256603422397/8527500000000000000 : ℝ)) (alpha := (35561057437/170550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-208863757/2000000000 : ℝ)*X 0 0+(5407898677/10000000000 : ℝ)*X 0 1+(5407898601/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5224317731/10000000000 : ℝ)*X 1 0+(-326202389/2500000000 : ℝ)*X 1 1+(5407898591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1306079403/2500000000 : ℝ)*X 2 0+(1351974687/2500000000 : ℝ)*X 2 1+(-1304809501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4462392591/10000000000 : ℝ)*X 0 0+(3913025973/10000000000 : ℝ)*X 0 1+(3913025983/10000000000 : ℝ)*X 0 2+(4462392591/10000000000 : ℝ)*X 1 0+(3913025973/10000000000 : ℝ)*X 1 1+(3913025983/10000000000 : ℝ)*X 1 2+(4462392591/10000000000 : ℝ)*X 2 0+(3913025973/10000000000 : ℝ)*X 2 1+(3913025983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1675243701/10000000000 : ℝ)*X 0 0+(1294491161/2500000000 : ℝ)*X 0 1+(1035592959/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5379595269/10000000000 : ℝ)*X 1 0+(-703527027/5000000000 : ℝ)*X 1 1+(1294491537/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2689797637/5000000000 : ℝ)*X 2 0+(2022643/3906250 : ℝ)*X 2 1+(-70352707/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((368556071/1000000000 : ℝ)*X 0 0+(1075160311/2500000000 : ℝ)*X 0 1+(430064101/1000000000 : ℝ)*X 0 2+(368556071/1000000000 : ℝ)*X 1 0+(1075160311/2500000000 : ℝ)*X 1 1+(430064101/1000000000 : ℝ)*X 1 2+(368556071/1000000000 : ℝ)*X 2 0+(1075160311/2500000000 : ℝ)*X 2 1+(430064101/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-307864943/2000000000 : ℝ)*X 0 0+(156481329/312500000 : ℝ)*X 0 1+(27249521/50000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2597987691/5000000000 : ℝ)*X 1 0+(-1285395597/10000000000 : ℝ)*X 1 1+(5449904417/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2597987599/5000000000 : ℝ)*X 2 0+(2724952211/5000000000 : ℝ)*X 2 1+(-321348961/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2299681049/5000000000 : ℝ)*X 0 0+(3842027777/10000000000 : ℝ)*X 0 1+(3842027249/10000000000 : ℝ)*X 0 2+(2299681049/5000000000 : ℝ)*X 1 0+(3842027777/10000000000 : ℝ)*X 1 1+(3842027249/10000000000 : ℝ)*X 1 2+(2299681049/5000000000 : ℝ)*X 2 0+(3842027777/10000000000 : ℝ)*X 2 1+(3842027249/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-146788463/1250000000 : ℝ)*X 0 0+(2785351401/5000000000 : ℝ)*X 0 1+(5153053241/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5396452599/10000000000 : ℝ)*X 1 0+(-708853417/5000000000 : ℝ)*X 1 1+(5153053333/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((269822633/500000000 : ℝ)*X 2 0+(2576526651/5000000000 : ℝ)*X 2 1+(-177213349/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1799206979/5000000000 : ℝ)*X 0 0+(4342522017/10000000000 : ℝ)*X 0 1+(217126111/500000000 : ℝ)*X 0 2+(1799206979/5000000000 : ℝ)*X 1 0+(4342522017/10000000000 : ℝ)*X 1 1+(217126111/500000000 : ℝ)*X 1 2+(1799206979/5000000000 : ℝ)*X 2 0+(4342522017/10000000000 : ℝ)*X 2 1+(217126111/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1728_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66923/100000 : ℝ) ≤ (-1268142151421216797813519269/1895000000000000000000000000 : ℝ) := by norm_num
    linear_combination (853577/5000000000000 : ℝ)*(upper1) + (2463477/25000000000000 : ℝ)*(upper3) + (2781781/25000000000000 : ℝ)*(lower4) + (175244074891479/12500000000000 : ℝ)*(major0) + (175244074891479/12500000000000 : ℝ)*(major1) + (175244074891479/12500000000000 : ℝ)*(major2) + (2128472569863409/100000000000000 : ℝ)*(sp4) + (532088519159779/25000000000000 : ℝ)*(sp5) + (66511290909167/3125000000000 : ℝ)*(sp6) + (697727266291137/100000000000000 : ℝ)*(sp7) + (681604427/100000000000000 : ℝ)*(sp12) + (119174828719/100000000000000 : ℝ)*(sp13) + (27985593623/25000000000000 : ℝ)*(sp14) + (1149055607/10000000000000 : ℝ)*(sp15) + (697738756847207/100000000000000 : ℝ)*(f.failure) + (532118312866959/25000000000000 : ℝ)*(f.sum) + (7359882699717/1895000000000000000000000000 : ℝ)*base65 + (16586980116991093/11843750000000000000000000000000 : ℝ)*base68 + (30760684303116093/11843750000000000000000000000000 : ℝ)*base70 + (115587827941977657/11843750000000000000000000000000 : ℝ)*base71 + (206390410577/473750000000000000000000000 : ℝ)*base74 + (99346089102915157/11843750000000000000000000000000 : ℝ)*base75 + (35958544635803593/11843750000000000000000000000000 : ℝ)*base78 + (13601219624696407/11843750000000000000000000000000 : ℝ)*base79 + (3825395586659/947500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2343193/1000000000000000000000 : ℝ)*base90 + (2343193/1000000000000000000000 : ℝ)*base92 + (2343193/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29411/50000 : ℝ) ≤ (20900970551907005273493681237727/35531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2565713/50000000000000 : ℝ)*(lower1) + (343477/50000000000000 : ℝ)*(upper2) + (583037/6250000000000 : ℝ)*(lower5) + (756001709694391/50000000000000 : ℝ)*(major0) + (756001709694391/50000000000000 : ℝ)*(major1) + (756001709694391/50000000000000 : ℝ)*(major2) + (1125944307227029/50000000000000 : ℝ)*(sp0) + (70371464273951/3125000000000 : ℝ)*(sp1) + (562971853325279/25000000000000 : ℝ)*(sp2) + (752509921722647/100000000000000 : ℝ)*(sp3) + (668041899/50000000000000 : ℝ)*(sp6) + (10382769/10000000000000 : ℝ)*(sp7) + (134930857/100000000000000 : ℝ)*(sp8) + (1892618483/100000000000000 : ℝ)*(sp9) + (1469746143653/195312500000 : ℝ)*(f.failure) + (450377749876983/20000000000000 : ℝ)*(f.sum) + (16255860277523/4263750000000000000000000000 : ℝ)*base66 + (3354332768574849773/426375000000000000000000000000000 : ℝ)*base68 + (1336441239445599773/426375000000000000000000000000000 : ℝ)*base70 + (2889974118442599773/426375000000000000000000000000000 : ℝ)*base72 + (9814970075417/1065937500000000000000000000 : ℝ)*base74 + (2920665038209974773/426375000000000000000000000000000 : ℝ)*base76 + (995775187718349773/426375000000000000000000000000000 : ℝ)*base78 + (30024402461900227/426375000000000000000000000000000 : ℝ)*base79 + (58302390900107/17055000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12769/3906250000000000000 : ℝ)*base90 + (12769/3906250000000000000 : ℝ)*base92 + (12769/3906250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (41023/50000 : ℝ) ≤ (29152893788819602197057593808523/35531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14699029/50000000000000 : ℝ)*(upper1) + (22409463/50000000000000 : ℝ)*(upper2) + (444003/1250000000000 : ℝ)*(upper3) + (28690509/100000000000000 : ℝ)*(lower5) + (761237071849391/50000000000000 : ℝ)*(major0) + (761237071849391/50000000000000 : ℝ)*(major1) + (761237071849391/50000000000000 : ℝ)*(major2) + (10216954443/100000000000000 : ℝ)*(sp1) + (2268690827/25000000000000 : ℝ)*(sp2) + (2392930793/100000000000000 : ℝ)*(sp3) + (45197550918797/2000000000000 : ℝ)*(sp8) + (1129933664492703/50000000000000 : ℝ)*(sp9) + (2259868471176541/100000000000000 : ℝ)*(sp10) + (378859407314729/50000000000000 : ℝ)*(sp11) + (757721207560251/100000000000000 : ℝ)*(f.failure) + (45197550918797/2000000000000 : ℝ)*(f.sum) + (16546056129367/17055000000000000000000000000 : ℝ)*base66 + (1783047256192064773/426375000000000000000000000000000 : ℝ)*base68 + (1327749224212185227/426375000000000000000000000000000 : ℝ)*base69 + (2151814457659560227/426375000000000000000000000000000 : ℝ)*base71 + (100391539593607/17055000000000000000000000000 : ℝ)*base74 + (4979029395429060227/426375000000000000000000000000000 : ℝ)*base75 + (1455200130637185227/426375000000000000000000000000000 : ℝ)*base77 + (2036350969664685227/426375000000000000000000000000000 : ℝ)*base79 + (73127141735227/17055000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1146949/1000000000000000000000 : ℝ)*base90 + (1146949/1000000000000000000000 : ℝ)*base92 + (1146949/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-45337/50000 : ℝ) ≤ (-25773233761561232572433143463017/28425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18422313/100000000000000 : ℝ)*(lower0) + (21541261/50000000000000 : ℝ)*(lower1) + (16654203/100000000000000 : ℝ)*(lower2) + (314732705720539/20000000000000 : ℝ)*(major0) + (314732705720539/20000000000000 : ℝ)*(major1) + (314732705720539/20000000000000 : ℝ)*(major2) + (845808679/100000000000000 : ℝ)*(sp0) + (3420690633/20000000000000 : ℝ)*(sp5) + (15888112979/100000000000000 : ℝ)*(sp6) + (618969751/25000000000000 : ℝ)*(sp7) + (1197176096276267/50000000000000 : ℝ)*(sp12) + (149645995931753/6250000000000 : ℝ)*(sp13) + (1197168575124117/50000000000000 : ℝ)*(sp14) + (783195211990743/100000000000000 : ℝ)*(sp15) + (195799421967437/25000000000000 : ℝ)*(f.failure) + (598588259590303/25000000000000 : ℝ)*(f.sum) + (4564081858627/3411000000000000000000000000 : ℝ)*base66 + (86064876165761983/170550000000000000000000000000000 : ℝ)*base67 + (568870440577488017/170550000000000000000000000000000 : ℝ)*base70 + (31613511888611983/170550000000000000000000000000000 : ℝ)*base71 + (4739482100771/3411000000000000000000000000 : ℝ)*base73 + (1728467456744538017/170550000000000000000000000000000 : ℝ)*base76 + (1022960335243338017/170550000000000000000000000000000 : ℝ)*base78 + (247855486794588017/170550000000000000000000000000000 : ℝ)*base80 + (690631195027/1705500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2621037/250000000000000000000 : ℝ)*base89 + (2621037/250000000000000000000 : ℝ)*base91 + (2621037/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1728_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16963/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10141/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66923/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29411/50000 : ℝ) else (41023/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45337/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1728_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1728_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66923/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29411/50000 : ℝ) else (41023/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45337/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1728_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1728_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5439/1024 : ℝ) ≤ p) (hpb : p ≤ (5447/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20092801/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16969/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1267/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66923/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29411/50000 : ℝ) else (41023/50000 : ℝ) ≤ X j i ∧ X j i ≤ (45337/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1728_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
