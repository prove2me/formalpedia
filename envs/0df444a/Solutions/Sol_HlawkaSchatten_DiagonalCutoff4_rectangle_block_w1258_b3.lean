-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:52:59.59568+00:00
-- url     : https://prove2.me/submissions/5dcb6279-c070-4cc7-b5b3-470d92e0094a

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
theorem support_rectangle_w1258_box_0 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-994711017/5000000000 : ℝ)*x 0 + (1074919879/2000000000 : ℝ)*x 1 + (20994529/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (994711017/5000000000 : ℝ)^8451 ≤ (11869288358893/100000000000000 : ℝ)^6403 := by
    have hnat : (994711017 : ℕ)^8451*100000000000000^6403 ≤ 11869288358893^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994711017 5000000000 11869288358893 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074919879/2000000000 : ℝ)^8451 ≤ (8813071130913/20000000000000 : ℝ)^6403 := by
    have hnat : (1074919879 : ℕ)^8451*20000000000000^6403 ≤ 8813071130913^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074919879 2000000000 8813071130913 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20994529/39062500 : ℝ)^8451 ≤ (2203267798419/5000000000000 : ℝ)^6403 := by
    have hnat : (20994529 : ℕ)^8451*5000000000000^6403 ≤ 2203267798419^6403*39062500^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20994529 39062500 2203267798419 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-994711017/5000000000 : ℝ), (1074919879/2000000000 : ℝ), (20994529/39062500 : ℝ)] ![(11869288358893/100000000000000 : ℝ), (8813071130913/20000000000000 : ℝ), (2203267798419/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-994711017/5000000000 : ℝ)|^8451 ≤ (11869288358893/100000000000000 : ℝ)^6403
        have hw : |(-994711017/5000000000 : ℝ)|=(994711017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074919879/2000000000 : ℝ)|^8451 ≤ (8813071130913/20000000000000 : ℝ)^6403
        have hw : |(1074919879/2000000000 : ℝ)|=(1074919879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(20994529/39062500 : ℝ)|^8451 ≤ (2203267798419/5000000000000 : ℝ)^6403
        have hw : |(20994529/39062500 : ℝ)|=(20994529/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_1 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648451429/5000000000 : ℝ)*x 0 + (-419011861/2000000000 : ℝ)*x 1 + (1343649857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648451429/5000000000 : ℝ)^8451 ≤ (4322653539783/10000000000000 : ℝ)^6403 := by
    have hnat : (2648451429 : ℕ)^8451*10000000000000^6403 ≤ 4322653539783^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648451429 5000000000 4322653539783 10000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (419011861/2000000000 : ℝ)^8451 ≤ (2541621714983/20000000000000 : ℝ)^6403 := by
    have hnat : (419011861 : ℕ)^8451*20000000000000^6403 ≤ 2541621714983^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419011861 2000000000 2541621714983 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1343649857/2500000000 : ℝ)^8451 ≤ (8813071202333/20000000000000 : ℝ)^6403 := by
    have hnat : (1343649857 : ℕ)^8451*20000000000000^6403 ≤ 8813071202333^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343649857 2500000000 8813071202333 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648451429/5000000000 : ℝ), (-419011861/2000000000 : ℝ), (1343649857/2500000000 : ℝ)] ![(4322653539783/10000000000000 : ℝ), (2541621714983/20000000000000 : ℝ), (8813071202333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648451429/5000000000 : ℝ)|^8451 ≤ (4322653539783/10000000000000 : ℝ)^6403
        have hw : |(2648451429/5000000000 : ℝ)|=(2648451429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-419011861/2000000000 : ℝ)|^8451 ≤ (2541621714983/20000000000000 : ℝ)^6403
        have hw : |(-419011861/2000000000 : ℝ)|=(419011861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1343649857/2500000000 : ℝ)|^8451 ≤ (8813071202333/20000000000000 : ℝ)^6403
        have hw : |(1343649857/2500000000 : ℝ)|=(1343649857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_2 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296902791/10000000000 : ℝ)*x 0 + (1074919889/2000000000 : ℝ)*x 1 + (-2095059373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296902791/10000000000 : ℝ)^8451 ≤ (21613267338089/50000000000000 : ℝ)^6403 := by
    have hnat : (5296902791 : ℕ)^8451*50000000000000^6403 ≤ 21613267338089^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296902791 10000000000 21613267338089 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074919889/2000000000 : ℝ)^8451 ≤ (70504569913/160000000000 : ℝ)^6403 := by
    have hnat : (1074919889 : ℕ)^8451*160000000000^6403 ≤ 70504569913^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074919889 2000000000 70504569913 160000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2095059373/10000000000 : ℝ)^8451 ≤ (2541621823863/20000000000000 : ℝ)^6403 := by
    have hnat : (2095059373 : ℕ)^8451*20000000000000^6403 ≤ 2541621823863^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095059373 10000000000 2541621823863 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296902791/10000000000 : ℝ), (1074919889/2000000000 : ℝ), (-2095059373/10000000000 : ℝ)] ![(21613267338089/50000000000000 : ℝ), (70504569913/160000000000 : ℝ), (2541621823863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296902791/10000000000 : ℝ)|^8451 ≤ (21613267338089/50000000000000 : ℝ)^6403
        have hw : |(5296902791/10000000000 : ℝ)|=(5296902791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074919889/2000000000 : ℝ)|^8451 ≤ (70504569913/160000000000 : ℝ)^6403
        have hw : |(1074919889/2000000000 : ℝ)|=(1074919889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2095059373/10000000000 : ℝ)|^8451 ≤ (2541621823863/20000000000000 : ℝ)^6403
        have hw : |(-2095059373/10000000000 : ℝ)|=(2095059373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_3 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4454958797/10000000000 : ℝ)*x 0 + (537178803/1250000000 : ℝ)*x 1 + (1074357629/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4454958797/10000000000 : ℝ)^8451 ≤ (17198727921081/50000000000000 : ℝ)^6403 := by
    have hnat : (4454958797 : ℕ)^8451*50000000000000^6403 ≤ 17198727921081^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4454958797 10000000000 17198727921081 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537178803/1250000000 : ℝ)^8451 ≤ (16400635803831/50000000000000 : ℝ)^6403 := by
    have hnat : (537178803 : ℕ)^8451*50000000000000^6403 ≤ 16400635803831^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537178803 1250000000 16400635803831 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074357629/2500000000 : ℝ)^8451 ≤ (410015906681/1250000000000 : ℝ)^6403 := by
    have hnat : (1074357629 : ℕ)^8451*1250000000000^6403 ≤ 410015906681^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074357629 2500000000 410015906681 1250000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4454958797/10000000000 : ℝ), (537178803/1250000000 : ℝ), (1074357629/2500000000 : ℝ)] ![(17198727921081/50000000000000 : ℝ), (16400635803831/50000000000000 : ℝ), (410015906681/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4454958797/10000000000 : ℝ)|^8451 ≤ (17198727921081/50000000000000 : ℝ)^6403
        have hw : |(4454958797/10000000000 : ℝ)|=(4454958797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537178803/1250000000 : ℝ)|^8451 ≤ (16400635803831/50000000000000 : ℝ)^6403
        have hw : |(537178803/1250000000 : ℝ)|=(537178803/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1074357629/2500000000 : ℝ)|^8451 ≤ (410015906681/1250000000000 : ℝ)^6403
        have hw : |(1074357629/2500000000 : ℝ)|=(1074357629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_4 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1118601001/5000000000 : ℝ)*x 0 + (660305583/1250000000 : ℝ)*x 1 + (2641222349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1118601001/5000000000 : ℝ)^8451 ≤ (1732281130067/12500000000000 : ℝ)^6403 := by
    have hnat : (1118601001 : ℕ)^8451*12500000000000^6403 ≤ 1732281130067^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118601001 5000000000 1732281130067 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660305583/1250000000 : ℝ)^8451 ≤ (43070875289399/100000000000000 : ℝ)^6403 := by
    have hnat : (660305583 : ℕ)^8451*100000000000000^6403 ≤ 43070875289399^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660305583 1250000000 43070875289399 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2641222349/5000000000 : ℝ)^8451 ≤ (43070875655291/100000000000000 : ℝ)^6403 := by
    have hnat : (2641222349 : ℕ)^8451*100000000000000^6403 ≤ 43070875655291^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641222349 5000000000 43070875655291 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1118601001/5000000000 : ℝ), (660305583/1250000000 : ℝ), (2641222349/5000000000 : ℝ)] ![(1732281130067/12500000000000 : ℝ), (43070875289399/100000000000000 : ℝ), (43070875655291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1118601001/5000000000 : ℝ)|^8451 ≤ (1732281130067/12500000000000 : ℝ)^6403
        have hw : |(-1118601001/5000000000 : ℝ)|=(1118601001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(660305583/1250000000 : ℝ)|^8451 ≤ (43070875289399/100000000000000 : ℝ)^6403
        have hw : |(660305583/1250000000 : ℝ)|=(660305583/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2641222349/5000000000 : ℝ)|^8451 ≤ (43070875655291/100000000000000 : ℝ)^6403
        have hw : |(2641222349/5000000000 : ℝ)|=(2641222349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_5 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5361842631/10000000000 : ℝ)*x 0 + (-33306829/156250000 : ℝ)*x 1 + (5282444669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361842631/10000000000 : ℝ)^8451 ≤ (1098184111857/2500000000000 : ℝ)^6403 := by
    have hnat : (5361842631 : ℕ)^8451*2500000000000^6403 ≤ 1098184111857^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361842631 10000000000 1098184111857 2500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33306829/156250000 : ℝ)^8451 ≤ (101576251327/781250000000 : ℝ)^6403 := by
    have hnat : (33306829 : ℕ)^8451*781250000000^6403 ≤ 101576251327^6403*156250000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33306829 156250000 101576251327 781250000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282444669/10000000000 : ℝ)^8451 ≤ (43070875343207/100000000000000 : ℝ)^6403 := by
    have hnat : (5282444669 : ℕ)^8451*100000000000000^6403 ≤ 43070875343207^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282444669 10000000000 43070875343207 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361842631/10000000000 : ℝ), (-33306829/156250000 : ℝ), (5282444669/10000000000 : ℝ)] ![(1098184111857/2500000000000 : ℝ), (101576251327/781250000000 : ℝ), (43070875343207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361842631/10000000000 : ℝ)|^8451 ≤ (1098184111857/2500000000000 : ℝ)^6403
        have hw : |(5361842631/10000000000 : ℝ)|=(5361842631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33306829/156250000 : ℝ)|^8451 ≤ (101576251327/781250000000 : ℝ)^6403
        have hw : |(-33306829/156250000 : ℝ)|=(33306829/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282444669/10000000000 : ℝ)|^8451 ≤ (43070875343207/100000000000000 : ℝ)^6403
        have hw : |(5282444669/10000000000 : ℝ)|=(5282444669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_6 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2680921323/5000000000 : ℝ)*x 0 + (1320611173/2500000000 : ℝ)*x 1 + (-426327401/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680921323/5000000000 : ℝ)^8451 ≤ (1757094585459/4000000000000 : ℝ)^6403 := by
    have hnat : (2680921323 : ℕ)^8451*4000000000000^6403 ≤ 1757094585459^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680921323 5000000000 1757094585459 4000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1320611173/2500000000 : ℝ)^8451 ≤ (21535437795361/50000000000000 : ℝ)^6403 := by
    have hnat : (1320611173 : ℕ)^8451*50000000000000^6403 ≤ 21535437795361^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320611173 2500000000 21535437795361 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426327401/2000000000 : ℝ)^8451 ≤ (1300175975929/10000000000000 : ℝ)^6403 := by
    have hnat : (426327401 : ℕ)^8451*10000000000000^6403 ≤ 1300175975929^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426327401 2000000000 1300175975929 10000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680921323/5000000000 : ℝ), (1320611173/2500000000 : ℝ), (-426327401/2000000000 : ℝ)] ![(1757094585459/4000000000000 : ℝ), (21535437795361/50000000000000 : ℝ), (1300175975929/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680921323/5000000000 : ℝ)|^8451 ≤ (1757094585459/4000000000000 : ℝ)^6403
        have hw : |(2680921323/5000000000 : ℝ)|=(2680921323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1320611173/2500000000 : ℝ)|^8451 ≤ (21535437795361/50000000000000 : ℝ)^6403
        have hw : |(1320611173/2500000000 : ℝ)|=(1320611173/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426327401/2000000000 : ℝ)|^8451 ≤ (1300175975929/10000000000000 : ℝ)^6403
        have hw : |(-426327401/2000000000 : ℝ)|=(426327401/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_7 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060450859/2500000000 : ℝ)*x 0 + (4403988151/10000000000 : ℝ)*x 1 + (275249261/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060450859/2500000000 : ℝ)^8451 ≤ (4030255380737/12500000000000 : ℝ)^6403 := by
    have hnat : (1060450859 : ℕ)^8451*12500000000000^6403 ≤ 4030255380737^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060450859 2500000000 4030255380737 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4403988151/10000000000 : ℝ)^8451 ≤ (1693948917221/5000000000000 : ℝ)^6403 := by
    have hnat : (4403988151 : ℕ)^8451*5000000000000^6403 ≤ 1693948917221^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403988151 10000000000 1693948917221 5000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (275249261/625000000 : ℝ)^8451 ≤ (33878978598253/100000000000000 : ℝ)^6403 := by
    have hnat : (275249261 : ℕ)^8451*100000000000000^6403 ≤ 33878978598253^6403*625000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275249261 625000000 33878978598253 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060450859/2500000000 : ℝ), (4403988151/10000000000 : ℝ), (275249261/625000000 : ℝ)] ![(4030255380737/12500000000000 : ℝ), (1693948917221/5000000000000 : ℝ), (33878978598253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060450859/2500000000 : ℝ)|^8451 ≤ (4030255380737/12500000000000 : ℝ)^6403
        have hw : |(1060450859/2500000000 : ℝ)|=(1060450859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4403988151/10000000000 : ℝ)|^8451 ≤ (1693948917221/5000000000000 : ℝ)^6403
        have hw : |(4403988151/10000000000 : ℝ)|=(4403988151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(275249261/625000000 : ℝ)|^8451 ≤ (33878978598253/100000000000000 : ℝ)^6403
        have hw : |(275249261/625000000 : ℝ)|=(275249261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_8 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2185263787/10000000000 : ℝ)*x 0 + (1304888977/2500000000 : ℝ)*x 1 + (673026563/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185263787/10000000000 : ℝ)^8451 ≤ (3358799993239/25000000000000 : ℝ)^6403 := by
    have hnat : (2185263787 : ℕ)^8451*25000000000000^6403 ≤ 3358799993239^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185263787 10000000000 3358799993239 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304888977/2500000000 : ℝ)^8451 ≤ (21197694579079/50000000000000 : ℝ)^6403 := by
    have hnat : (1304888977 : ℕ)^8451*50000000000000^6403 ≤ 21197694579079^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304888977 2500000000 21197694579079 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673026563/1250000000 : ℝ)^8451 ≤ (276058817869/625000000000 : ℝ)^6403 := by
    have hnat : (673026563 : ℕ)^8451*625000000000^6403 ≤ 276058817869^6403*1250000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673026563 1250000000 276058817869 625000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2185263787/10000000000 : ℝ), (1304888977/2500000000 : ℝ), (673026563/1250000000 : ℝ)] ![(3358799993239/25000000000000 : ℝ), (21197694579079/50000000000000 : ℝ), (276058817869/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2185263787/10000000000 : ℝ)|^8451 ≤ (3358799993239/25000000000000 : ℝ)^6403
        have hw : |(-2185263787/10000000000 : ℝ)|=(2185263787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304888977/2500000000 : ℝ)|^8451 ≤ (21197694579079/50000000000000 : ℝ)^6403
        have hw : |(1304888977/2500000000 : ℝ)|=(1304888977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673026563/1250000000 : ℝ)|^8451 ≤ (276058817869/625000000000 : ℝ)^6403
        have hw : |(673026563/1250000000 : ℝ)|=(673026563/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_9 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5290126253/10000000000 : ℝ)*x 0 + (-522794199/2500000000 : ℝ)*x 1 + (5384211969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290126253/10000000000 : ℝ)^8451 ≤ (5394195003597/12500000000000 : ℝ)^6403 := by
    have hnat : (5290126253 : ℕ)^8451*12500000000000^6403 ≤ 5394195003597^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290126253 10000000000 5394195003597 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522794199/2500000000 : ℝ)^8451 ≤ (2535406976221/20000000000000 : ℝ)^6403 := by
    have hnat : (522794199 : ℕ)^8451*20000000000000^6403 ≤ 2535406976221^6403*2500000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522794199 2500000000 2535406976221 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384211969/10000000000 : ℝ)^8451 ≤ (44169405066383/100000000000000 : ℝ)^6403 := by
    have hnat : (5384211969 : ℕ)^8451*100000000000000^6403 ≤ 44169405066383^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384211969 10000000000 44169405066383 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290126253/10000000000 : ℝ), (-522794199/2500000000 : ℝ), (5384211969/10000000000 : ℝ)] ![(5394195003597/12500000000000 : ℝ), (2535406976221/20000000000000 : ℝ), (44169405066383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290126253/10000000000 : ℝ)|^8451 ≤ (5394195003597/12500000000000 : ℝ)^6403
        have hw : |(5290126253/10000000000 : ℝ)|=(5290126253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522794199/2500000000 : ℝ)|^8451 ≤ (2535406976221/20000000000000 : ℝ)^6403
        have hw : |(-522794199/2500000000 : ℝ)|=(522794199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384211969/10000000000 : ℝ)|^8451 ≤ (44169405066383/100000000000000 : ℝ)^6403
        have hw : |(5384211969/10000000000 : ℝ)|=(5384211969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_10 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66126571/125000000 : ℝ)*x 0 + (1076842633/2000000000 : ℝ)*x 1 + (-41823519/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66126571/125000000 : ℝ)^8451 ≤ (43153553859563/100000000000000 : ℝ)^6403 := by
    have hnat : (66126571 : ℕ)^8451*100000000000000^6403 ≤ 43153553859563^6403*125000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66126571 125000000 43153553859563 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076842633/2000000000 : ℝ)^8451 ≤ (11042354503987/25000000000000 : ℝ)^6403 := by
    have hnat : (1076842633 : ℕ)^8451*25000000000000^6403 ≤ 11042354503987^6403*2000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076842633 2000000000 11042354503987 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41823519/200000000 : ℝ)^8451 ≤ (12677028112147/100000000000000 : ℝ)^6403 := by
    have hnat : (41823519 : ℕ)^8451*100000000000000^6403 ≤ 12677028112147^6403*200000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41823519 200000000 12677028112147 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66126571/125000000 : ℝ), (1076842633/2000000000 : ℝ), (-41823519/200000000 : ℝ)] ![(43153553859563/100000000000000 : ℝ), (11042354503987/25000000000000 : ℝ), (12677028112147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66126571/125000000 : ℝ)|^8451 ≤ (43153553859563/100000000000000 : ℝ)^6403
        have hw : |(66126571/125000000 : ℝ)|=(66126571/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076842633/2000000000 : ℝ)|^8451 ≤ (11042354503987/25000000000000 : ℝ)^6403
        have hw : |(1076842633/2000000000 : ℝ)|=(1076842633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41823519/200000000 : ℝ)|^8451 ≤ (12677028112147/100000000000000 : ℝ)^6403
        have hw : |(-41823519/200000000 : ℝ)|=(41823519/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_11 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (179076877/400000000 : ℝ)*x 0 + (2143154219/5000000000 : ℝ)*x 1 + (2143154151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (179076877/400000000 : ℝ)^8451 ≤ (34621453418809/100000000000000 : ℝ)^6403 := by
    have hnat : (179076877 : ℕ)^8451*100000000000000^6403 ≤ 34621453418809^6403*400000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179076877 400000000 34621453418809 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2143154219/5000000000 : ℝ)^8451 ≤ (32689273966699/100000000000000 : ℝ)^6403 := by
    have hnat : (2143154219 : ℕ)^8451*100000000000000^6403 ≤ 32689273966699^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143154219 5000000000 32689273966699 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2143154151/5000000000 : ℝ)^8451 ≤ (8172318149439/25000000000000 : ℝ)^6403 := by
    have hnat : (2143154151 : ℕ)^8451*25000000000000^6403 ≤ 8172318149439^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143154151 5000000000 8172318149439 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(179076877/400000000 : ℝ), (2143154219/5000000000 : ℝ), (2143154151/5000000000 : ℝ)] ![(34621453418809/100000000000000 : ℝ), (32689273966699/100000000000000 : ℝ), (8172318149439/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(179076877/400000000 : ℝ)|^8451 ≤ (34621453418809/100000000000000 : ℝ)^6403
        have hw : |(179076877/400000000 : ℝ)|=(179076877/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2143154219/5000000000 : ℝ)|^8451 ≤ (32689273966699/100000000000000 : ℝ)^6403
        have hw : |(2143154219/5000000000 : ℝ)|=(2143154219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2143154151/5000000000 : ℝ)|^8451 ≤ (8172318149439/25000000000000 : ℝ)^6403
        have hw : |(2143154151/5000000000 : ℝ)|=(2143154151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_12 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2041611057/10000000000 : ℝ)*x 0 + (2718145149/5000000000 : ℝ)*x 1 + (2637179737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2041611057/10000000000 : ℝ)^8451 ≤ (3070491053037/25000000000000 : ℝ)^6403 := by
    have hnat : (2041611057 : ℕ)^8451*25000000000000^6403 ≤ 3070491053037^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2041611057 10000000000 3070491053037 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718145149/5000000000 : ℝ)^8451 ≤ (11183537014649/25000000000000 : ℝ)^6403 := by
    have hnat : (2718145149 : ℕ)^8451*25000000000000^6403 ≤ 11183537014649^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718145149 5000000000 11183537014649 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637179737/5000000000 : ℝ)^8451 ≤ (21491943858011/50000000000000 : ℝ)^6403 := by
    have hnat : (2637179737 : ℕ)^8451*50000000000000^6403 ≤ 21491943858011^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637179737 5000000000 21491943858011 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2041611057/10000000000 : ℝ), (2718145149/5000000000 : ℝ), (2637179737/5000000000 : ℝ)] ![(3070491053037/25000000000000 : ℝ), (11183537014649/25000000000000 : ℝ), (21491943858011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2041611057/10000000000 : ℝ)|^8451 ≤ (3070491053037/25000000000000 : ℝ)^6403
        have hw : |(-2041611057/10000000000 : ℝ)|=(2041611057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718145149/5000000000 : ℝ)|^8451 ≤ (11183537014649/25000000000000 : ℝ)^6403
        have hw : |(2718145149/5000000000 : ℝ)|=(2718145149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637179737/5000000000 : ℝ)|^8451 ≤ (21491943858011/50000000000000 : ℝ)^6403
        have hw : |(2637179737/5000000000 : ℝ)|=(2637179737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_13 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367538381/10000000000 : ℝ)*x 0 + (-2134790157/10000000000 : ℝ)*x 1 + (5274359437/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367538381/10000000000 : ℝ)^8451 ≤ (10997240751441/25000000000000 : ℝ)^6403 := by
    have hnat : (5367538381 : ℕ)^8451*25000000000000^6403 ≤ 10997240751441^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367538381 10000000000 10997240751441 25000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2134790157/10000000000 : ℝ)^8451 ≤ (1628393708099/12500000000000 : ℝ)^6403 := by
    have hnat : (2134790157 : ℕ)^8451*12500000000000^6403 ≤ 1628393708099^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134790157 10000000000 1628393708099 12500000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274359437/10000000000 : ℝ)^8451 ≤ (42983887318041/100000000000000 : ℝ)^6403 := by
    have hnat : (5274359437 : ℕ)^8451*100000000000000^6403 ≤ 42983887318041^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274359437 10000000000 42983887318041 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367538381/10000000000 : ℝ), (-2134790157/10000000000 : ℝ), (5274359437/10000000000 : ℝ)] ![(10997240751441/25000000000000 : ℝ), (1628393708099/12500000000000 : ℝ), (42983887318041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367538381/10000000000 : ℝ)|^8451 ≤ (10997240751441/25000000000000 : ℝ)^6403
        have hw : |(5367538381/10000000000 : ℝ)|=(5367538381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2134790157/10000000000 : ℝ)|^8451 ≤ (1628393708099/12500000000000 : ℝ)^6403
        have hw : |(-2134790157/10000000000 : ℝ)|=(2134790157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274359437/10000000000 : ℝ)|^8451 ≤ (42983887318041/100000000000000 : ℝ)^6403
        have hw : |(5274359437/10000000000 : ℝ)|=(5274359437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_14 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2683769197/5000000000 : ℝ)*x 0 + (210974379/400000000 : ℝ)*x 1 + (-2134790087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2683769197/5000000000 : ℝ)^8451 ≤ (43988963146381/100000000000000 : ℝ)^6403 := by
    have hnat : (2683769197 : ℕ)^8451*100000000000000^6403 ≤ 43988963146381^6403*5000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2683769197 5000000000 43988963146381 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210974379/400000000 : ℝ)^8451 ≤ (21491943863389/50000000000000 : ℝ)^6403 := by
    have hnat : (210974379 : ℕ)^8451*50000000000000^6403 ≤ 21491943863389^6403*400000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210974379 400000000 21491943863389 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2134790087/10000000000 : ℝ)^8451 ≤ (6513574550501/50000000000000 : ℝ)^6403 := by
    have hnat : (2134790087 : ℕ)^8451*50000000000000^6403 ≤ 6513574550501^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2134790087 10000000000 6513574550501 50000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2683769197/5000000000 : ℝ), (210974379/400000000 : ℝ), (-2134790087/10000000000 : ℝ)] ![(43988963146381/100000000000000 : ℝ), (21491943863389/50000000000000 : ℝ), (6513574550501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2683769197/5000000000 : ℝ)|^8451 ≤ (43988963146381/100000000000000 : ℝ)^6403
        have hw : |(2683769197/5000000000 : ℝ)|=(2683769197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210974379/400000000 : ℝ)|^8451 ≤ (21491943863389/50000000000000 : ℝ)^6403
        have hw : |(210974379/400000000 : ℝ)|=(210974379/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2134790087/10000000000 : ℝ)|^8451 ≤ (6513574550501/50000000000000 : ℝ)^6403
        have hw : |(-2134790087/10000000000 : ℝ)|=(2134790087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1258_box_15 (p : ℝ) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4222870359/10000000000 : ℝ)*x 0 + (4413331943/10000000000 : ℝ)*x 1 + (441333189/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4222870359/10000000000 : ℝ)^8451 ≤ (6410447632431/20000000000000 : ℝ)^6403 := by
    have hnat : (4222870359 : ℕ)^8451*20000000000000^6403 ≤ 6410447632431^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222870359 10000000000 6410447632431 20000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4413331943/10000000000 : ℝ)^8451 ≤ (33973881180053/100000000000000 : ℝ)^6403 := by
    have hnat : (4413331943 : ℕ)^8451*100000000000000^6403 ≤ 33973881180053^6403*10000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4413331943 10000000000 33973881180053 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441333189/1000000000 : ℝ)^8451 ≤ (33973880641561/100000000000000 : ℝ)^6403 := by
    have hnat : (441333189 : ℕ)^8451*100000000000000^6403 ≤ 33973880641561^6403*1000000000^8451 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441333189 1000000000 33973880641561 100000000000000 8451 6403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8451/2048 : ℝ)) 8451 6403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4222870359/10000000000 : ℝ), (4413331943/10000000000 : ℝ), (441333189/1000000000 : ℝ)] ![(6410447632431/20000000000000 : ℝ), (33973881180053/100000000000000 : ℝ), (33973880641561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4222870359/10000000000 : ℝ)|^8451 ≤ (6410447632431/20000000000000 : ℝ)^6403
        have hw : |(4222870359/10000000000 : ℝ)|=(4222870359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4413331943/10000000000 : ℝ)|^8451 ≤ (33973881180053/100000000000000 : ℝ)^6403
        have hw : |(4413331943/10000000000 : ℝ)|=(4413331943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441333189/1000000000 : ℝ)|^8451 ≤ (33973880641561/100000000000000 : ℝ)^6403
        have hw : |(441333189/1000000000 : ℝ)|=(441333189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1258_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5749/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(249/400 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5939/10000 : ℝ) ∧ (20039/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83381/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5749/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (441/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5749/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5749/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (441/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5749/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5749/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (441/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5749/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5749/50000 : ℝ) ^ (4225/1024 : ℝ) ≤ (1330912929802507/10000000000000000000 : ℝ) := by
    have hpowers : (5749/50000 : ℝ)^4225 ≤ (1330912929802507/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5749 : ℕ)^4225*10000000000000000000^1024 ≤ 1330912929802507^1024*50000^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5749 50000 1330912929802507 10000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5749/50000 : ℝ)) (X := (1330912929802507/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (441/3125 : ℝ) ^ (4225/1024 : ℝ) ≤ (30990056084663839/100000000000000000000 : ℝ) := by
    have hpowers : (441/3125 : ℝ)^4225 ≤ (30990056084663839/100000000000000000000 : ℝ)^1024 := by
      have hnat : (441 : ℕ)^4225*100000000000000000000^1024 ≤ 30990056084663839^1024*3125^4225 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        441 3125 30990056084663839 100000000000000000000 4225 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (441/3125 : ℝ)) (X := (30990056084663839/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001330912929802507/5000000000000000000 : ℝ) ≤ (10000645073343873/10000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (5001330912929802507/5000000000000000000 : ℝ)^1024 ≤ (10000645073343873/10000000000000000 : ℝ)^4225 := by
      have hnat : (5001330912929802507 : ℕ)^1024*10000000000000000^4225 ≤ 10000645073343873^4225*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001330912929802507 5000000000000000000 10000645073343873 10000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000645073343873/10000000000000000 : ℝ)) (X := (5001330912929802507/5000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044299185382688909/100000000000000000000 : ℝ) ≤ (5000536742667787/5000000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (100044299185382688909/100000000000000000000 : ℝ)^1024 ≤ (5000536742667787/5000000000000000 : ℝ)^4225 := by
      have hnat : (100044299185382688909 : ℕ)^1024*5000000000000000^4225 ≤ 5000536742667787^4225*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044299185382688909 100000000000000000000 5000536742667787 5000000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000536742667787/5000000000000000 : ℝ)) (X := (100044299185382688909/100000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030990056084663839/50000000000000000000 : ℝ) ≤ (400060075893091/400000000000000 : ℝ) ^ (4225/1024 : ℝ) := by
    have hpowers : (50030990056084663839/50000000000000000000 : ℝ)^1024 ≤ (400060075893091/400000000000000 : ℝ)^4225 := by
      have hnat : (50030990056084663839 : ℕ)^1024*400000000000000^4225 ≤ 400060075893091^4225*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030990056084663839 50000000000000000000 400060075893091 400000000000000 1024 4225 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400060075893091/400000000000000 : ℝ)) (X := (50030990056084663839/50000000000000000000 : ℝ)) (by norm_num) 4225 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1330912929802507/10000000000000000000 : ℝ) ≤ ((13065917229779863913/13070000000000000000 : ℝ)+2*(428411991701/261400000000000 : ℝ)*(5749/50000 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (13065917229779863913/13070000000000000000 : ℝ)+2*(428411991701/261400000000000 : ℝ)*(5749/50000 : ℝ)=(10000645073343873/10000000000000000 : ℝ) by norm_num, show 1+2*(1330912929802507/10000000000000000000 : ℝ)=(5001330912929802507/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30990056084663839/100000000000000000000 : ℝ)+(1330912929802507/10000000000000000000 : ℝ) ≤ ((13065917229779863913/13070000000000000000 : ℝ)+(428411991701/261400000000000 : ℝ)*((441/3125 : ℝ)+(5749/50000 : ℝ)))^(4225/1024 : ℝ) := by
    rw [show (13065917229779863913/13070000000000000000 : ℝ)+(428411991701/261400000000000 : ℝ)*((441/3125 : ℝ)+(5749/50000 : ℝ))=(5000536742667787/5000000000000000 : ℝ) by norm_num, show 1+(30990056084663839/100000000000000000000 : ℝ)+(1330912929802507/10000000000000000000 : ℝ)=(100044299185382688909/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30990056084663839/100000000000000000000 : ℝ) ≤ ((13065917229779863913/13070000000000000000 : ℝ)+2*(428411991701/261400000000000 : ℝ)*(441/3125 : ℝ))^(4225/1024 : ℝ) := by
    rw [show (13065917229779863913/13070000000000000000 : ℝ)+2*(428411991701/261400000000000 : ℝ)*(441/3125 : ℝ)=(400060075893091/400000000000000 : ℝ) by norm_num, show 1+2*(30990056084663839/100000000000000000000 : ℝ)=(50030990056084663839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13065917229779863913/13070000000000000000 : ℝ)*(X 1 0+X 2 0)+(428411991701/261400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5749/50000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (13065917229779863913/13070000000000000000 : ℝ)) (alpha := (428411991701/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13065917229779863913/13070000000000000000 : ℝ)*(X 0 1+X 2 1)+(428411991701/261400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5749/50000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (13065917229779863913/13070000000000000000 : ℝ)) (alpha := (428411991701/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13065917229779863913/13070000000000000000 : ℝ)*(X 0 2+X 1 2)+(428411991701/261400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4225/1024 : ℝ)) (lo := (5749/50000 : ℝ)) (hi := (441/3125 : ℝ)) (c := (13065917229779863913/13070000000000000000 : ℝ)) (alpha := (428411991701/261400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-994711017/5000000000 : ℝ)*X 0 0+(1074919879/2000000000 : ℝ)*X 0 1+(20994529/39062500 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2648451429/5000000000 : ℝ)*X 1 0+(-419011861/2000000000 : ℝ)*X 1 1+(1343649857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296902791/10000000000 : ℝ)*X 2 0+(1074919889/2000000000 : ℝ)*X 2 1+(-2095059373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4454958797/10000000000 : ℝ)*X 0 0+(537178803/1250000000 : ℝ)*X 0 1+(1074357629/2500000000 : ℝ)*X 0 2+(4454958797/10000000000 : ℝ)*X 1 0+(537178803/1250000000 : ℝ)*X 1 1+(1074357629/2500000000 : ℝ)*X 1 2+(4454958797/10000000000 : ℝ)*X 2 0+(537178803/1250000000 : ℝ)*X 2 1+(1074357629/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1118601001/5000000000 : ℝ)*X 0 0+(660305583/1250000000 : ℝ)*X 0 1+(2641222349/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5361842631/10000000000 : ℝ)*X 1 0+(-33306829/156250000 : ℝ)*X 1 1+(5282444669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2680921323/5000000000 : ℝ)*X 2 0+(1320611173/2500000000 : ℝ)*X 2 1+(-426327401/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1060450859/2500000000 : ℝ)*X 0 0+(4403988151/10000000000 : ℝ)*X 0 1+(275249261/625000000 : ℝ)*X 0 2+(1060450859/2500000000 : ℝ)*X 1 0+(4403988151/10000000000 : ℝ)*X 1 1+(275249261/625000000 : ℝ)*X 1 2+(1060450859/2500000000 : ℝ)*X 2 0+(4403988151/10000000000 : ℝ)*X 2 1+(275249261/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2185263787/10000000000 : ℝ)*X 0 0+(1304888977/2500000000 : ℝ)*X 0 1+(673026563/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5290126253/10000000000 : ℝ)*X 1 0+(-522794199/2500000000 : ℝ)*X 1 1+(5384211969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((66126571/125000000 : ℝ)*X 2 0+(1076842633/2000000000 : ℝ)*X 2 1+(-41823519/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((179076877/400000000 : ℝ)*X 0 0+(2143154219/5000000000 : ℝ)*X 0 1+(2143154151/5000000000 : ℝ)*X 0 2+(179076877/400000000 : ℝ)*X 1 0+(2143154219/5000000000 : ℝ)*X 1 1+(2143154151/5000000000 : ℝ)*X 1 2+(179076877/400000000 : ℝ)*X 2 0+(2143154219/5000000000 : ℝ)*X 2 1+(2143154151/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2041611057/10000000000 : ℝ)*X 0 0+(2718145149/5000000000 : ℝ)*X 0 1+(2637179737/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367538381/10000000000 : ℝ)*X 1 0+(-2134790157/10000000000 : ℝ)*X 1 1+(5274359437/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2683769197/5000000000 : ℝ)*X 2 0+(210974379/400000000 : ℝ)*X 2 1+(-2134790087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4222870359/10000000000 : ℝ)*X 0 0+(4413331943/10000000000 : ℝ)*X 0 1+(441333189/1000000000 : ℝ)*X 0 2+(4222870359/10000000000 : ℝ)*X 1 0+(4413331943/10000000000 : ℝ)*X 1 1+(441333189/1000000000 : ℝ)*X 1 2+(4222870359/10000000000 : ℝ)*X 2 0+(4413331943/10000000000 : ℝ)*X 2 1+(441333189/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1258_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-249/400 : ℝ) ≤ (-25424153655119804639193844131621/40843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3737759/12500000000000 : ℝ)*(upper0) + (11288687/20000000000000 : ℝ)*(upper1) + (10161169/100000000000000 : ℝ)*(upper3) + (18865099/25000000000000 : ℝ)*(upper5) + (502031404066739/12500000000000 : ℝ)*(major0) + (502031404066739/12500000000000 : ℝ)*(major1) + (502031404066739/12500000000000 : ℝ)*(major2) + (9990453/800000000000 : ℝ)*(sp2) + (1730878051/50000000000000 : ℝ)*(sp3) + (1351621256287677/25000000000000 : ℝ)*(sp4) + (1351622008083753/25000000000000 : ℝ)*(sp5) + (2703243391764193/50000000000000 : ℝ)*(sp6) + (132338004449069/5000000000000 : ℝ)*(sp7) + (3007184303/100000000000000 : ℝ)*(sp8) + (1323381775368741/50000000000000 : ℝ)*(f.failure) + (1351622008083753/25000000000000 : ℝ)*(f.sum) + (11665079468261/6535000000000000000000000000 : ℝ)*base65 + (552155222310639707/163375000000000000000000000000000 : ℝ)*base67 + (13763930434639707/163375000000000000000000000000000 : ℝ)*base69 + (151376358986110293/163375000000000000000000000000000 : ℝ)*base72 + (3116903479337/816875000000000000000000000 : ℝ)*base73 + (5962120226369139707/163375000000000000000000000000000 : ℝ)*base75 + (833343064912264707/163375000000000000000000000000000 : ℝ)*base77 + (5313651633147264707/163375000000000000000000000000000 : ℝ)*base79 + (275518296510661/6535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (38134007/5000000000000000000000 : ℝ)*base90 + (38134007/5000000000000000000000 : ℝ)*base92 + (38134007/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5939/10000 : ℝ) ≤ (4851647470535234883652517915889/8168750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (53029773/100000000000000 : ℝ)*(upper2) + (2119119/50000000000000 : ℝ)*(upper3) + (1183153/100000000000000 : ℝ)*(upper5) + (102057824114851/2500000000000 : ℝ)*(major0) + (102057824114851/2500000000000 : ℝ)*(major1) + (102057824114851/2500000000000 : ℝ)*(major2) + (5454526033899833/100000000000000 : ℝ)*(sp0) + (272726298890501/5000000000000 : ℝ)*(sp1) + (5454528516228723/100000000000000 : ℝ)*(sp2) + (1345148785723371/50000000000000 : ℝ)*(sp3) + (1619423387/50000000000000 : ℝ)*(sp5) + (700428071/100000000000000 : ℝ)*(sp6) + (1548753863/100000000000000 : ℝ)*(sp7) + (19892231/625000000000 : ℝ)*(sp12) + (1345149560100303/50000000000000 : ℝ)*(f.failure) + (2727264608328397/50000000000000 : ℝ)*(f.sum) + (2480348994251/326750000000000000000000000 : ℝ)*base65 + (180469688438521963/32675000000000000000000000000000 : ℝ)*base67 + (301816806348778037/32675000000000000000000000000000 : ℝ)*base70 + (241936085214478037/32675000000000000000000000000000 : ℝ)*base72 + (2176793269753/261400000000000000000000000 : ℝ)*base73 + (199801572402228037/32675000000000000000000000000000 : ℝ)*base76 + (97098338262853037/32675000000000000000000000000000 : ℝ)*base78 + (127924566733078037/32675000000000000000000000000000 : ℝ)*base80 + (545581345339/653500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (55117819/5000000000000000000000 : ℝ)*base89 + (55117819/5000000000000000000000 : ℝ)*base91 + (55117819/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (20039/25000 : ℝ) ≤ (261917649187989213972727998578847/326750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (472883563/100000000000000 : ℝ)*(lower3) + (45397943/20000000000000 : ℝ)*(upper4) + (164667807/50000000000000 : ℝ)*(lower5) + (2274450918722173/50000000000000 : ℝ)*(major0) + (2274450918722173/50000000000000 : ℝ)*(major1) + (2274450918722173/50000000000000 : ℝ)*(major2) + (36678638597/100000000000000 : ℝ)*(sp0) + (95303446301/50000000000000 : ℝ)*(sp1) + (519510733271/50000000000000 : ℝ)*(sp2) + (211449304709/50000000000000 : ℝ)*(sp3) + (6073260062174523/100000000000000 : ℝ)*(sp8) + (3036553066960259/50000000000000 : ℝ)*(sp9) + (6072257719346579/100000000000000 : ℝ)*(sp10) + (74934114023129/2500000000000 : ℝ)*(sp11) + (1498893729767289/50000000000000 : ℝ)*(f.failure) + (18979052315041/312500000000 : ℝ)*(f.sum) + (1515013827633/408437500000000000000000000 : ℝ)*base65 + (10412262986079207051/653500000000000000000000000000000 : ℝ)*base68 + (2448494839138707051/653500000000000000000000000000000 : ℝ)*base70 + (5307885559203292949/653500000000000000000000000000000 : ℝ)*base71 + (58108837242817/6535000000000000000000000000 : ℝ)*base74 + (3583501062588292949/653500000000000000000000000000000 : ℝ)*base75 + (2207986489148707051/653500000000000000000000000000000 : ℝ)*base78 + (6397943856570207051/653500000000000000000000000000000 : ℝ)*base80 + (8111731129447/6535000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (36278803/5000000000000000000000 : ℝ)*base90 + (36278803/5000000000000000000000 : ℝ)*base92 + (36278803/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-83381/100000 : ℝ) ≤ (-68109513350066189444549447264931/81687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12490479/50000000000000 : ℝ)*(lower0) + (1222377/10000000000000 : ℝ)*(upper1) + (5413/32000000000 : ℝ)*(lower2) + (11900161/20000000000000 : ℝ)*(upper5) + (1146111593203029/25000000000000 : ℝ)*(major0) + (1146111593203029/25000000000000 : ℝ)*(major1) + (1146111593203029/25000000000000 : ℝ)*(major2) + (307739919/12500000000000 : ℝ)*(sp4) + (15603758349/100000000000000 : ℝ)*(sp5) + (6619799201/25000000000000 : ℝ)*(sp7) + (385966950559071/6250000000000 : ℝ)*(sp12) + (6175458067106139/100000000000000 : ℝ)*(sp13) + (771934208858061/12500000000000 : ℝ)*(sp14) + (3021185306952909/100000000000000 : ℝ)*(sp15) + (3021211786149713/100000000000000 : ℝ)*(f.failure) + (771934208858061/12500000000000 : ℝ)*(f.sum) + (25818992198507/6535000000000000000000000000 : ℝ)*base66 + (2018518075008592477/326750000000000000000000000000000 : ℝ)*base67 + (5046705778036342477/326750000000000000000000000000000 : ℝ)*base69 + (2781815810198092477/326750000000000000000000000000000 : ℝ)*base71 + (7483442557909/3267500000000000000000000000 : ℝ)*base73 + (1429334600374342477/326750000000000000000000000000000 : ℝ)*base75 + (1902980316766407523/326750000000000000000000000000000 : ℝ)*base78 + (3357541031006592477/326750000000000000000000000000000 : ℝ)*base79 + (1098412075157/1633750000000000000000000000 : ℝ)*base81 + (75996251/10000000000000000000000 : ℝ)*base90 + (75996251/10000000000000000000000 : ℝ)*base92 + (75996251/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1258_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5749/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(5939/10000 : ℝ) else (20039/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83381/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1258_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1258_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5749/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(5939/10000 : ℝ) else (20039/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83381/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1258_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4225/1024 : ℝ) ≤ p) (hpb : p ≤ (8451/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151741973/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (441/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5749/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(249/400 : ℝ) ≤ X j i ∧ X j i ≤ -(5939/10000 : ℝ) else (20039/25000 : ℝ) ≤ X j i ∧ X j i ≤ (83381/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1258_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
