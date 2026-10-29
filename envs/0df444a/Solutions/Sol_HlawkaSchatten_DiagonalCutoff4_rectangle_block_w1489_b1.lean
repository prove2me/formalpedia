-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1489_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:15:01.530286+00:00
-- url     : https://prove2.me/submissions/47170464-2911-4e5f-b098-9460eeef337a

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
theorem support_rectangle_w1489_s3_0 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901885419/10000000000 : ℝ)*x 0 + (5440494899/10000000000 : ℝ)*x 1 + (5212565059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901885419/10000000000 : ℝ)^4475 ≤ (11622509285907/100000000000000 : ℝ)^3451 := by
    have hnat : (1901885419 : ℕ)^4475*100000000000000^3451 ≤ 11622509285907^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901885419 10000000000 11622509285907 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5440494899/10000000000 : ℝ)^4475 ≤ (567682585459/1250000000000 : ℝ)^3451 := by
    have hnat : (5440494899 : ℕ)^4475*1250000000000^3451 ≤ 567682585459^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440494899 10000000000 567682585459 1250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212565059/10000000000 : ℝ)^4475 ≤ (42962883858051/100000000000000 : ℝ)^3451 := by
    have hnat : (5212565059 : ℕ)^4475*100000000000000^3451 ≤ 42962883858051^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212565059 10000000000 42962883858051 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901885419/10000000000 : ℝ), (5440494899/10000000000 : ℝ), (5212565059/10000000000 : ℝ)] ![(11622509285907/100000000000000 : ℝ), (567682585459/1250000000000 : ℝ), (42962883858051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901885419/10000000000 : ℝ)|^4475 ≤ (11622509285907/100000000000000 : ℝ)^3451
        have hw : |(-1901885419/10000000000 : ℝ)|=(1901885419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5440494899/10000000000 : ℝ)|^4475 ≤ (567682585459/1250000000000 : ℝ)^3451
        have hw : |(5440494899/10000000000 : ℝ)|=(5440494899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212565059/10000000000 : ℝ)|^4475 ≤ (42962883858051/100000000000000 : ℝ)^3451
        have hw : |(5212565059/10000000000 : ℝ)|=(5212565059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s3_1 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353945051/10000000000 : ℝ)*x 0 + (-126173683/625000000 : ℝ)*x 1 + (2606282559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353945051/10000000000 : ℝ)^4475 ≤ (22239986564161/50000000000000 : ℝ)^3451 := by
    have hnat : (5353945051 : ℕ)^4475*50000000000000^3451 ≤ 22239986564161^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353945051 10000000000 22239986564161 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126173683/625000000 : ℝ)^4475 ≤ (12557142373611/100000000000000 : ℝ)^3451 := by
    have hnat : (126173683 : ℕ)^4475*100000000000000^3451 ≤ 12557142373611^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126173683 625000000 12557142373611 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606282559/5000000000 : ℝ)^4475 ≤ (42962884488633/100000000000000 : ℝ)^3451 := by
    have hnat : (2606282559 : ℕ)^4475*100000000000000^3451 ≤ 42962884488633^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606282559 5000000000 42962884488633 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353945051/10000000000 : ℝ), (-126173683/625000000 : ℝ), (2606282559/5000000000 : ℝ)] ![(22239986564161/50000000000000 : ℝ), (12557142373611/100000000000000 : ℝ), (42962884488633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353945051/10000000000 : ℝ)|^4475 ≤ (22239986564161/50000000000000 : ℝ)^3451
        have hw : |(5353945051/10000000000 : ℝ)|=(5353945051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-126173683/625000000 : ℝ)|^4475 ≤ (12557142373611/100000000000000 : ℝ)^3451
        have hw : |(-126173683/625000000 : ℝ)|=(126173683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606282559/5000000000 : ℝ)|^4475 ≤ (42962884488633/100000000000000 : ℝ)^3451
        have hw : |(2606282559/5000000000 : ℝ)|=(2606282559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s3_2 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676972403/5000000000 : ℝ)*x 0 + (2606282763/5000000000 : ℝ)*x 1 + (-1009389357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676972403/5000000000 : ℝ)^4475 ≤ (1779198819557/4000000000000 : ℝ)^3451 := by
    have hnat : (2676972403 : ℕ)^4475*4000000000000^3451 ≤ 1779198819557^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676972403 5000000000 1779198819557 4000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606282763/5000000000 : ℝ)^4475 ≤ (42962888849273/100000000000000 : ℝ)^3451 := by
    have hnat : (2606282763 : ℕ)^4475*100000000000000^3451 ≤ 42962888849273^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606282763 5000000000 42962888849273 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009389357/5000000000 : ℝ)^4475 ≤ (12557140647519/100000000000000 : ℝ)^3451 := by
    have hnat : (1009389357 : ℕ)^4475*100000000000000^3451 ≤ 12557140647519^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009389357 5000000000 12557140647519 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676972403/5000000000 : ℝ), (2606282763/5000000000 : ℝ), (-1009389357/5000000000 : ℝ)] ![(1779198819557/4000000000000 : ℝ), (42962888849273/100000000000000 : ℝ), (12557140647519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676972403/5000000000 : ℝ)|^4475 ≤ (1779198819557/4000000000000 : ℝ)^3451
        have hw : |(2676972403/5000000000 : ℝ)|=(2676972403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606282763/5000000000 : ℝ)|^4475 ≤ (42962888849273/100000000000000 : ℝ)^3451
        have hw : |(2606282763/5000000000 : ℝ)|=(2606282763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1009389357/5000000000 : ℝ)|^4475 ≤ (12557140647519/100000000000000 : ℝ)^3451
        have hw : |(-1009389357/5000000000 : ℝ)|=(1009389357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s3_3 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34241583/80000000 : ℝ)*x 0 + (4032490251/10000000000 : ℝ)*x 1 + (908194843/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34241583/80000000 : ℝ)^4475 ≤ (16637181142763/50000000000000 : ℝ)^3451 := by
    have hnat : (34241583 : ℕ)^4475*50000000000000^3451 ≤ 16637181142763^3451*80000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34241583 80000000 16637181142763 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4032490251/10000000000 : ℝ)^4475 ≤ (3079901588901/10000000000000 : ℝ)^3451 := by
    have hnat : (4032490251 : ℕ)^4475*10000000000000^3451 ≤ 3079901588901^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4032490251 10000000000 3079901588901 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (908194843/2000000000 : ℝ)^4475 ≤ (17963310906747/50000000000000 : ℝ)^3451 := by
    have hnat : (908194843 : ℕ)^4475*50000000000000^3451 ≤ 17963310906747^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      908194843 2000000000 17963310906747 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34241583/80000000 : ℝ), (4032490251/10000000000 : ℝ), (908194843/2000000000 : ℝ)] ![(16637181142763/50000000000000 : ℝ), (3079901588901/10000000000000 : ℝ), (17963310906747/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34241583/80000000 : ℝ)|^4475 ≤ (16637181142763/50000000000000 : ℝ)^3451
        have hw : |(34241583/80000000 : ℝ)|=(34241583/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4032490251/10000000000 : ℝ)|^4475 ≤ (3079901588901/10000000000000 : ℝ)^3451
        have hw : |(4032490251/10000000000 : ℝ)|=(4032490251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(908194843/2000000000 : ℝ)|^4475 ≤ (17963310906747/50000000000000 : ℝ)^3451
        have hw : |(908194843/2000000000 : ℝ)|=(908194843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s3_4 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1901918293/10000000000 : ℝ)*x 0 + (5213776003/10000000000 : ℝ)*x 1 + (339954693/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1901918293/10000000000 : ℝ)^4475 ≤ (363211555989/3125000000000 : ℝ)^3451 := by
    have hnat : (1901918293 : ℕ)^4475*3125000000000^3451 ≤ 363211555989^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1901918293 10000000000 363211555989 3125000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213776003/10000000000 : ℝ)^4475 ≤ (42975826682019/100000000000000 : ℝ)^3451 := by
    have hnat : (5213776003 : ℕ)^4475*100000000000000^3451 ≤ 42975826682019^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213776003 10000000000 42975826682019 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339954693/625000000 : ℝ)^4475 ≤ (22700701755617/50000000000000 : ℝ)^3451 := by
    have hnat : (339954693 : ℕ)^4475*50000000000000^3451 ≤ 22700701755617^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339954693 625000000 22700701755617 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1901918293/10000000000 : ℝ), (5213776003/10000000000 : ℝ), (339954693/625000000 : ℝ)] ![(363211555989/3125000000000 : ℝ), (42975826682019/100000000000000 : ℝ), (22700701755617/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1901918293/10000000000 : ℝ)|^4475 ≤ (363211555989/3125000000000 : ℝ)^3451
        have hw : |(-1901918293/10000000000 : ℝ)|=(1901918293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213776003/10000000000 : ℝ)|^4475 ≤ (42975826682019/100000000000000 : ℝ)^3451
        have hw : |(5213776003/10000000000 : ℝ)|=(5213776003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339954693/625000000 : ℝ)|^4475 ≤ (22700701755617/50000000000000 : ℝ)^3451
        have hw : |(339954693/625000000 : ℝ)|=(339954693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s3_5 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (52943253/100000000 : ℝ)*x 0 + (-71682759/400000000 : ℝ)*x 1 + (5439275301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52943253/100000000 : ℝ)^4475 ≤ (10959687617449/25000000000000 : ℝ)^3451 := by
    have hnat : (52943253 : ℕ)^4475*25000000000000^3451 ≤ 10959687617449^3451*100000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52943253 100000000 10959687617449 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71682759/400000000 : ℝ)^4475 ≤ (5379921850521/50000000000000 : ℝ)^3451 := by
    have hnat : (71682759 : ℕ)^4475*50000000000000^3451 ≤ 5379921850521^3451*400000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71682759 400000000 5379921850521 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5439275301/10000000000 : ℝ)^4475 ≤ (9080281163337/20000000000000 : ℝ)^3451 := by
    have hnat : (5439275301 : ℕ)^4475*20000000000000^3451 ≤ 9080281163337^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439275301 10000000000 9080281163337 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(52943253/100000000 : ℝ), (-71682759/400000000 : ℝ), (5439275301/10000000000 : ℝ)] ![(10959687617449/25000000000000 : ℝ), (5379921850521/50000000000000 : ℝ), (9080281163337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(52943253/100000000 : ℝ)|^4475 ≤ (10959687617449/25000000000000 : ℝ)^3451
        have hw : |(52943253/100000000 : ℝ)|=(52943253/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71682759/400000000 : ℝ)|^4475 ≤ (5379921850521/50000000000000 : ℝ)^3451
        have hw : |(-71682759/400000000 : ℝ)|=(71682759/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5439275301/10000000000 : ℝ)|^4475 ≤ (9080281163337/20000000000000 : ℝ)^3451
        have hw : |(5439275301/10000000000 : ℝ)|=(5439275301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s3_6 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330895343/625000000 : ℝ)*x 0 + (5439275111/10000000000 : ℝ)*x 1 + (-89603449/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330895343/625000000 : ℝ)^4475 ≤ (43838752488411/100000000000000 : ℝ)^3451 := by
    have hnat : (330895343 : ℕ)^4475*100000000000000^3451 ≤ 43838752488411^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330895343 625000000 43838752488411 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439275111/10000000000 : ℝ)^4475 ≤ (45401403760179/100000000000000 : ℝ)^3451 := by
    have hnat : (5439275111 : ℕ)^4475*100000000000000^3451 ≤ 45401403760179^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439275111 10000000000 45401403760179 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89603449/500000000 : ℝ)^4475 ≤ (1075984373997/10000000000000 : ℝ)^3451 := by
    have hnat : (89603449 : ℕ)^4475*10000000000000^3451 ≤ 1075984373997^3451*500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89603449 500000000 1075984373997 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330895343/625000000 : ℝ), (5439275111/10000000000 : ℝ), (-89603449/500000000 : ℝ)] ![(43838752488411/100000000000000 : ℝ), (45401403760179/100000000000000 : ℝ), (1075984373997/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330895343/625000000 : ℝ)|^4475 ≤ (43838752488411/100000000000000 : ℝ)^3451
        have hw : |(330895343/625000000 : ℝ)|=(330895343/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439275111/10000000000 : ℝ)|^4475 ≤ (45401403760179/100000000000000 : ℝ)^3451
        have hw : |(5439275111/10000000000 : ℝ)|=(5439275111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-89603449/500000000 : ℝ)|^4475 ≤ (1075984373997/10000000000000 : ℝ)^3451
        have hw : |(-89603449/500000000 : ℝ)|=(89603449/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s3_7 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280272461/10000000000 : ℝ)*x 0 + (2269136747/5000000000 : ℝ)*x 1 + (4035211401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280272461/10000000000 : ℝ)^4475 ≤ (6655022834449/20000000000000 : ℝ)^3451 := by
    have hnat : (4280272461 : ℕ)^4475*20000000000000^3451 ≤ 6655022834449^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280272461 10000000000 6655022834449 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269136747/5000000000 : ℝ)^4475 ≤ (35898916898631/100000000000000 : ℝ)^3451 := by
    have hnat : (2269136747 : ℕ)^4475*100000000000000^3451 ≤ 35898916898631^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269136747 5000000000 35898916898631 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035211401/10000000000 : ℝ)^4475 ≤ (30825968916071/100000000000000 : ℝ)^3451 := by
    have hnat : (4035211401 : ℕ)^4475*100000000000000^3451 ≤ 30825968916071^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035211401 10000000000 30825968916071 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280272461/10000000000 : ℝ), (2269136747/5000000000 : ℝ), (4035211401/10000000000 : ℝ)] ![(6655022834449/20000000000000 : ℝ), (35898916898631/100000000000000 : ℝ), (30825968916071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280272461/10000000000 : ℝ)|^4475 ≤ (6655022834449/20000000000000 : ℝ)^3451
        have hw : |(4280272461/10000000000 : ℝ)|=(4280272461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2269136747/5000000000 : ℝ)|^4475 ≤ (35898916898631/100000000000000 : ℝ)^3451
        have hw : |(2269136747/5000000000 : ℝ)|=(2269136747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035211401/10000000000 : ℝ)|^4475 ≤ (30825968916071/100000000000000 : ℝ)^3451
        have hw : |(4035211401/10000000000 : ℝ)|=(4035211401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1489_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1609/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5371/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7783/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1609/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1609/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1609/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1609/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1609/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1609/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10261/100000 : ℝ) ^ (4473/1024 : ℝ) ≤ (2397089961203119/50000000000000000000 : ℝ) := by
    have hpowers : (10261/100000 : ℝ)^4473 ≤ (2397089961203119/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10261 : ℕ)^4473*50000000000000000000^1024 ≤ 2397089961203119^1024*100000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10261 100000 2397089961203119 50000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10261/100000 : ℝ)) (X := (2397089961203119/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1609/10000 : ℝ) ^ (4473/1024 : ℝ) ≤ (1710317071158737/5000000000000000000 : ℝ) := by
    have hpowers : (1609/10000 : ℝ)^4473 ≤ (1710317071158737/5000000000000000000 : ℝ)^1024 := by
      have hnat : (1609 : ℕ)^4473*5000000000000000000^1024 ≤ 1710317071158737^1024*10000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1609 10000 1710317071158737 5000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1609/10000 : ℝ)) (X := (1710317071158737/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002397089961203119/25000000000000000000 : ℝ) ≤ (1250027437171771/1250000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (25002397089961203119/25000000000000000000 : ℝ)^1024 ≤ (1250027437171771/1250000000000000 : ℝ)^4473 := by
      have hnat : (25002397089961203119 : ℕ)^1024*1250000000000000^4473 ≤ 1250027437171771^4473*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002397089961203119 25000000000000000000 1250027437171771 1250000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250027437171771/1250000000000000 : ℝ)) (X := (25002397089961203119/25000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019500260672790489/50000000000000000000 : ℝ) ≤ (2500223175331711/2500000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (50019500260672790489/50000000000000000000 : ℝ)^1024 ≤ (2500223175331711/2500000000000000 : ℝ)^4473 := by
      have hnat : (50019500260672790489 : ℕ)^1024*2500000000000000^4473 ≤ 2500223175331711^4473*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019500260672790489 50000000000000000000 2500223175331711 2500000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500223175331711/2500000000000000 : ℝ)) (X := (50019500260672790489/50000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501710317071158737/2500000000000000000 : ℝ) ≤ (62509786907997/62500000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (2501710317071158737/2500000000000000000 : ℝ)^1024 ≤ (62509786907997/62500000000000 : ℝ)^4473 := by
      have hnat : (2501710317071158737 : ℕ)^1024*62500000000000^4473 ≤ 62509786907997^4473*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501710317071158737 2500000000000000000 62509786907997 62500000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62509786907997/62500000000000 : ℝ)) (X := (2501710317071158737/2500000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2397089961203119/50000000000000000000 : ℝ) ≤ ((145693659896693021/145725000000000000 : ℝ)+2*(168300988169/145725000000000 : ℝ)*(10261/100000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (145693659896693021/145725000000000000 : ℝ)+2*(168300988169/145725000000000 : ℝ)*(10261/100000 : ℝ)=(1250027437171771/1250000000000000 : ℝ) by norm_num, show 1+2*(2397089961203119/50000000000000000000 : ℝ)=(25002397089961203119/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1710317071158737/5000000000000000000 : ℝ)+(2397089961203119/50000000000000000000 : ℝ) ≤ ((145693659896693021/145725000000000000 : ℝ)+(168300988169/145725000000000 : ℝ)*((1609/10000 : ℝ)+(10261/100000 : ℝ)))^(4473/1024 : ℝ) := by
    rw [show (145693659896693021/145725000000000000 : ℝ)+(168300988169/145725000000000 : ℝ)*((1609/10000 : ℝ)+(10261/100000 : ℝ))=(2500223175331711/2500000000000000 : ℝ) by norm_num, show 1+(1710317071158737/5000000000000000000 : ℝ)+(2397089961203119/50000000000000000000 : ℝ)=(50019500260672790489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1710317071158737/5000000000000000000 : ℝ) ≤ ((145693659896693021/145725000000000000 : ℝ)+2*(168300988169/145725000000000 : ℝ)*(1609/10000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (145693659896693021/145725000000000000 : ℝ)+2*(168300988169/145725000000000 : ℝ)*(1609/10000 : ℝ)=(62509786907997/62500000000000 : ℝ) by norm_num, show 1+2*(1710317071158737/5000000000000000000 : ℝ)=(2501710317071158737/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (145693659896693021/145725000000000000 : ℝ)*(X 1 0+X 2 0)+(168300988169/145725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10261/100000 : ℝ)) (hi := (1609/10000 : ℝ)) (c := (145693659896693021/145725000000000000 : ℝ)) (alpha := (168300988169/145725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (145693659896693021/145725000000000000 : ℝ)*(X 0 1+X 2 1)+(168300988169/145725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10261/100000 : ℝ)) (hi := (1609/10000 : ℝ)) (c := (145693659896693021/145725000000000000 : ℝ)) (alpha := (168300988169/145725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (145693659896693021/145725000000000000 : ℝ)*(X 0 2+X 1 2)+(168300988169/145725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10261/100000 : ℝ)) (hi := (1609/10000 : ℝ)) (c := (145693659896693021/145725000000000000 : ℝ)) (alpha := (168300988169/145725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1901885419/10000000000 : ℝ)*X 0 0+(5440494899/10000000000 : ℝ)*X 0 1+(5212565059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353945051/10000000000 : ℝ)*X 1 0+(-126173683/625000000 : ℝ)*X 1 1+(2606282559/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676972403/5000000000 : ℝ)*X 2 0+(2606282763/5000000000 : ℝ)*X 2 1+(-1009389357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((34241583/80000000 : ℝ)*X 0 0+(4032490251/10000000000 : ℝ)*X 0 1+(908194843/2000000000 : ℝ)*X 0 2+(34241583/80000000 : ℝ)*X 1 0+(4032490251/10000000000 : ℝ)*X 1 1+(908194843/2000000000 : ℝ)*X 1 2+(34241583/80000000 : ℝ)*X 2 0+(4032490251/10000000000 : ℝ)*X 2 1+(908194843/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1901918293/10000000000 : ℝ)*X 0 0+(5213776003/10000000000 : ℝ)*X 0 1+(339954693/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((52943253/100000000 : ℝ)*X 1 0+(-71682759/400000000 : ℝ)*X 1 1+(5439275301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330895343/625000000 : ℝ)*X 2 0+(5439275111/10000000000 : ℝ)*X 2 1+(-89603449/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4280272461/10000000000 : ℝ)*X 0 0+(2269136747/5000000000 : ℝ)*X 0 1+(4035211401/10000000000 : ℝ)*X 0 2+(4280272461/10000000000 : ℝ)*X 1 0+(2269136747/5000000000 : ℝ)*X 1 1+(4035211401/10000000000 : ℝ)*X 1 2+(4280272461/10000000000 : ℝ)*X 2 0+(2269136747/5000000000 : ℝ)*X 2 1+(4035211401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1396342771441944763661317/242875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84652757/5000000000000 : ℝ)*(base19) + (75667749/6250000000000 : ℝ)*(base23) + (45817463/20000000000000 : ℝ)*(upper3) + (15076839/10000000000000 : ℝ)*(upper4) + (2457/1280000000 : ℝ)*(upper5) + (635401822637527/20000000000000 : ℝ)*(major0) + (635401822637527/20000000000000 : ℝ)*(major1) + (635401822637527/20000000000000 : ℝ)*(major2) + (68552200440789/1562500000000 : ℝ)*(sp0) + (2193682962161091/50000000000000 : ℝ)*(sp1) + (2193683203346669/50000000000000 : ℝ)*(sp2) + (983320000582743/50000000000000 : ℝ)*(sp3) + (26789166827/100000000000000 : ℝ)*(sp4) + (1302023957/12500000000000 : ℝ)*(sp7) + (983325208678571/50000000000000 : ℝ)*(f.failure) + (2193683808688661/50000000000000 : ℝ)*(f.sum) + (11749023809947/5829000000000000000000000000 : ℝ)*base66 + (29715704923645433/2914500000000000000000000000000 : ℝ)*base68 + (56371789397234933/2914500000000000000000000000000 : ℝ)*base70 + (22472570617283933/2914500000000000000000000000000 : ℝ)*base72 + (12889009911707/2914500000000000000000000000 : ℝ)*base74 + (860006843043067/2914500000000000000000000000000 : ℝ)*base75 + (4319552417300933/2914500000000000000000000000000 : ℝ)*base78 + (22575627016688933/2914500000000000000000000000000 : ℝ)*base80 + (16413643174577/2914500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (7659641/5000000000000000000000 : ℝ)*base89 + (7659641/5000000000000000000000 : ℝ)*base91 + (7659641/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39122100135035199346967/9715000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56578749/12500000000000 : ℝ)*(base19) + (199078677/25000000000000 : ℝ)*(base23) + (2780931/4000000000000 : ℝ)*(upper3) + (84376791/100000000000000 : ℝ)*(lower4) + (87550341/100000000000000 : ℝ)*(upper5) + (1605608460112181/50000000000000 : ℝ)*(major0) + (1605608460112181/50000000000000 : ℝ)*(major1) + (1605608460112181/50000000000000 : ℝ)*(major2) + (10205361969/100000000000000 : ℝ)*(sp1) + (2517794003/20000000000000 : ℝ)*(sp2) + (2217303887896701/50000000000000 : ℝ)*(sp4) + (2217298558900721/50000000000000 : ℝ)*(sp5) + (110864859762717/2500000000000 : ℝ)*(sp6) + (496956482605671/25000000000000 : ℝ)*(sp7) + (496956482605671/25000000000000 : ℝ)*(f.failure) + (2217303887896701/50000000000000 : ℝ)*(f.sum) + (81934035838649/14572500000000000000000000000 : ℝ)*base66 + (81843283835680301/7286250000000000000000000000000 : ℝ)*base67 + (41306818081202801/7286250000000000000000000000000 : ℝ)*base69 + (11958796320944051/7286250000000000000000000000000 : ℝ)*base71 + (28774934506591/14572500000000000000000000000 : ℝ)*base73 + (76239426162087199/7286250000000000000000000000000 : ℝ)*base76 + (3779357305579699/7286250000000000000000000000000 : ℝ)*base78 + (6734449091764699/7286250000000000000000000000000 : ℝ)*base80 + (14148749831759/14572500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8406259/2500000000000000000000 : ℝ)*base90 + (8406259/2500000000000000000000 : ℝ)*base92 + (8406259/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1489_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1609/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7783/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1489_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1489_s4_0 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-951227057/5000000000 : ℝ)*x 0 + (5436796579/10000000000 : ℝ)*x 1 + (5215888283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951227057/5000000000 : ℝ)^4475 ≤ (2906754005969/25000000000000 : ℝ)^3451 := by
    have hnat : (951227057 : ℕ)^4475*25000000000000^3451 ≤ 2906754005969^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951227057 5000000000 2906754005969 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436796579/10000000000 : ℝ)^4475 ≤ (45374578650783/100000000000000 : ℝ)^3451 := by
    have hnat : (5436796579 : ℕ)^4475*100000000000000^3451 ≤ 45374578650783^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436796579 10000000000 45374578650783 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215888283/10000000000 : ℝ)^4475 ≤ (21499202654763/50000000000000 : ℝ)^3451 := by
    have hnat : (5215888283 : ℕ)^4475*50000000000000^3451 ≤ 21499202654763^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215888283 10000000000 21499202654763 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-951227057/5000000000 : ℝ), (5436796579/10000000000 : ℝ), (5215888283/10000000000 : ℝ)] ![(2906754005969/25000000000000 : ℝ), (45374578650783/100000000000000 : ℝ), (21499202654763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-951227057/5000000000 : ℝ)|^4475 ≤ (2906754005969/25000000000000 : ℝ)^3451
        have hw : |(-951227057/5000000000 : ℝ)|=(951227057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436796579/10000000000 : ℝ)|^4475 ≤ (45374578650783/100000000000000 : ℝ)^3451
        have hw : |(5436796579/10000000000 : ℝ)|=(5436796579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215888283/10000000000 : ℝ)|^4475 ≤ (21499202654763/50000000000000 : ℝ)^3451
        have hw : |(5215888283/10000000000 : ℝ)|=(5215888283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s4_1 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535298247/1000000000 : ℝ)*x 0 + (-2015659227/10000000000 : ℝ)*x 1 + (5215888853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535298247/1000000000 : ℝ)^4475 ≤ (1778784138857/4000000000000 : ℝ)^3451 := by
    have hnat : (535298247 : ℕ)^4475*4000000000000^3451 ≤ 1778784138857^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535298247 1000000000 1778784138857 4000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015659227/10000000000 : ℝ)^4475 ≤ (12531985104863/100000000000000 : ℝ)^3451 := by
    have hnat : (2015659227 : ℕ)^4475*100000000000000^3451 ≤ 12531985104863^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015659227 10000000000 12531985104863 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215888853/10000000000 : ℝ)^4475 ≤ (10749602850687/25000000000000 : ℝ)^3451 := by
    have hnat : (5215888853 : ℕ)^4475*25000000000000^3451 ≤ 10749602850687^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215888853 10000000000 10749602850687 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535298247/1000000000 : ℝ), (-2015659227/10000000000 : ℝ), (5215888853/10000000000 : ℝ)] ![(1778784138857/4000000000000 : ℝ), (12531985104863/100000000000000 : ℝ), (10749602850687/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535298247/1000000000 : ℝ)|^4475 ≤ (1778784138857/4000000000000 : ℝ)^3451
        have hw : |(535298247/1000000000 : ℝ)|=(535298247/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2015659227/10000000000 : ℝ)|^4475 ≤ (12531985104863/100000000000000 : ℝ)^3451
        have hw : |(-2015659227/10000000000 : ℝ)|=(2015659227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215888853/10000000000 : ℝ)|^4475 ≤ (10749602850687/25000000000000 : ℝ)^3451
        have hw : |(5215888853/10000000000 : ℝ)|=(5215888853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s4_2 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352982577/10000000000 : ℝ)*x 0 + (1043177687/2000000000 : ℝ)*x 1 + (-2015659639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352982577/10000000000 : ℝ)^4475 ≤ (555870057801/1250000000000 : ℝ)^3451 := by
    have hnat : (5352982577 : ℕ)^4475*1250000000000^3451 ≤ 555870057801^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352982577 10000000000 555870057801 1250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043177687/2000000000 : ℝ)^4475 ≤ (21499203467193/50000000000000 : ℝ)^3451 := by
    have hnat : (1043177687 : ℕ)^4475*50000000000000^3451 ≤ 21499203467193^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043177687 2000000000 21499203467193 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015659639/10000000000 : ℝ)^4475 ≤ (3132997106617/25000000000000 : ℝ)^3451 := by
    have hnat : (2015659639 : ℕ)^4475*25000000000000^3451 ≤ 3132997106617^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015659639 10000000000 3132997106617 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352982577/10000000000 : ℝ), (1043177687/2000000000 : ℝ), (-2015659639/10000000000 : ℝ)] ![(555870057801/1250000000000 : ℝ), (21499203467193/50000000000000 : ℝ), (3132997106617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352982577/10000000000 : ℝ)|^4475 ≤ (555870057801/1250000000000 : ℝ)^3451
        have hw : |(5352982577/10000000000 : ℝ)|=(5352982577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043177687/2000000000 : ℝ)|^4475 ≤ (21499203467193/50000000000000 : ℝ)^3451
        have hw : |(1043177687/2000000000 : ℝ)|=(1043177687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015659639/10000000000 : ℝ)|^4475 ≤ (3132997106617/25000000000000 : ℝ)^3451
        have hw : |(-2015659639/10000000000 : ℝ)|=(2015659639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s4_3 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428055329/1000000000 : ℝ)*x 0 + (4040280867/10000000000 : ℝ)*x 1 + (4533099929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428055329/1000000000 : ℝ)^4475 ≤ (6655589037749/20000000000000 : ℝ)^3451 := by
    have hnat : (428055329 : ℕ)^4475*20000000000000^3451 ≤ 6655589037749^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428055329 1000000000 6655589037749 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4040280867/10000000000 : ℝ)^4475 ≤ (30876196426869/100000000000000 : ℝ)^3451 := by
    have hnat : (4040280867 : ℕ)^4475*100000000000000^3451 ≤ 30876196426869^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4040280867 10000000000 30876196426869 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4533099929/10000000000 : ℝ)^4475 ≤ (2240366148199/6250000000000 : ℝ)^3451 := by
    have hnat : (4533099929 : ℕ)^4475*6250000000000^3451 ≤ 2240366148199^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533099929 10000000000 2240366148199 6250000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428055329/1000000000 : ℝ), (4040280867/10000000000 : ℝ), (4533099929/10000000000 : ℝ)] ![(6655589037749/20000000000000 : ℝ), (30876196426869/100000000000000 : ℝ), (2240366148199/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428055329/1000000000 : ℝ)|^4475 ≤ (6655589037749/20000000000000 : ℝ)^3451
        have hw : |(428055329/1000000000 : ℝ)|=(428055329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4040280867/10000000000 : ℝ)|^4475 ≤ (30876196426869/100000000000000 : ℝ)^3451
        have hw : |(4040280867/10000000000 : ℝ)|=(4040280867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4533099929/10000000000 : ℝ)|^4475 ≤ (2240366148199/6250000000000 : ℝ)^3451
        have hw : |(4533099929/10000000000 : ℝ)|=(4533099929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s4_4 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-190248449/1000000000 : ℝ)*x 0 + (5217025997/10000000000 : ℝ)*x 1 + (5435650467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (190248449/1000000000 : ℝ)^4475 ≤ (11627256755849/100000000000000 : ℝ)^3451 := by
    have hnat : (190248449 : ℕ)^4475*100000000000000^3451 ≤ 11627256755849^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190248449 1000000000 11627256755849 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217025997/10000000000 : ℝ)^4475 ≤ (2150528385507/5000000000000 : ℝ)^3451 := by
    have hnat : (5217025997 : ℕ)^4475*5000000000000^3451 ≤ 2150528385507^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217025997 10000000000 2150528385507 5000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435650467/10000000000 : ℝ)^4475 ≤ (45362175527013/100000000000000 : ℝ)^3451 := by
    have hnat : (5435650467 : ℕ)^4475*100000000000000^3451 ≤ 45362175527013^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435650467 10000000000 45362175527013 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-190248449/1000000000 : ℝ), (5217025997/10000000000 : ℝ), (5435650467/10000000000 : ℝ)] ![(11627256755849/100000000000000 : ℝ), (2150528385507/5000000000000 : ℝ), (45362175527013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-190248449/1000000000 : ℝ)|^4475 ≤ (11627256755849/100000000000000 : ℝ)^3451
        have hw : |(-190248449/1000000000 : ℝ)|=(190248449/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217025997/10000000000 : ℝ)|^4475 ≤ (2150528385507/5000000000000 : ℝ)^3451
        have hw : |(5217025997/10000000000 : ℝ)|=(5217025997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435650467/10000000000 : ℝ)|^4475 ≤ (45362175527013/100000000000000 : ℝ)^3451
        have hw : |(5435650467/10000000000 : ℝ)|=(5435650467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s4_5 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132380047/250000000 : ℝ)*x 0 + (-1795897587/10000000000 : ℝ)*x 1 + (5435650463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132380047/250000000 : ℝ)^4475 ≤ (21924081407539/50000000000000 : ℝ)^3451 := by
    have hnat : (132380047 : ℕ)^4475*50000000000000^3451 ≤ 21924081407539^3451*250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132380047 250000000 21924081407539 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1795897587/10000000000 : ℝ)^4475 ≤ (1078966168273/10000000000000 : ℝ)^3451 := by
    have hnat : (1795897587 : ℕ)^4475*10000000000000^3451 ≤ 1078966168273^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1795897587 10000000000 1078966168273 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435650463/10000000000 : ℝ)^4475 ≤ (45362175483727/100000000000000 : ℝ)^3451 := by
    have hnat : (5435650463 : ℕ)^4475*100000000000000^3451 ≤ 45362175483727^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435650463 10000000000 45362175483727 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132380047/250000000 : ℝ), (-1795897587/10000000000 : ℝ), (5435650463/10000000000 : ℝ)] ![(21924081407539/50000000000000 : ℝ), (1078966168273/10000000000000 : ℝ), (45362175483727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132380047/250000000 : ℝ)|^4475 ≤ (21924081407539/50000000000000 : ℝ)^3451
        have hw : |(132380047/250000000 : ℝ)|=(132380047/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1795897587/10000000000 : ℝ)|^4475 ≤ (1078966168273/10000000000000 : ℝ)^3451
        have hw : |(-1795897587/10000000000 : ℝ)|=(1795897587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435650463/10000000000 : ℝ)|^4475 ≤ (45362175483727/100000000000000 : ℝ)^3451
        have hw : |(5435650463/10000000000 : ℝ)|=(5435650463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s4_6 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295201863/10000000000 : ℝ)*x 0 + (2717825237/5000000000 : ℝ)*x 1 + (-359179519/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295201863/10000000000 : ℝ)^4475 ≤ (21924081316267/50000000000000 : ℝ)^3451 := by
    have hnat : (5295201863 : ℕ)^4475*50000000000000^3451 ≤ 21924081316267^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295201863 10000000000 21924081316267 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717825237/5000000000 : ℝ)^4475 ≤ (11340543900691/25000000000000 : ℝ)^3451 := by
    have hnat : (2717825237 : ℕ)^4475*25000000000000^3451 ≤ 11340543900691^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717825237 5000000000 11340543900691 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (359179519/2000000000 : ℝ)^4475 ≤ (2157932349011/20000000000000 : ℝ)^3451 := by
    have hnat : (359179519 : ℕ)^4475*20000000000000^3451 ≤ 2157932349011^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      359179519 2000000000 2157932349011 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295201863/10000000000 : ℝ), (2717825237/5000000000 : ℝ), (-359179519/2000000000 : ℝ)] ![(21924081316267/50000000000000 : ℝ), (11340543900691/25000000000000 : ℝ), (2157932349011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295201863/10000000000 : ℝ)|^4475 ≤ (21924081316267/50000000000000 : ℝ)^3451
        have hw : |(5295201863/10000000000 : ℝ)|=(5295201863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717825237/5000000000 : ℝ)|^4475 ≤ (11340543900691/25000000000000 : ℝ)^3451
        have hw : |(2717825237/5000000000 : ℝ)|=(2717825237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-359179519/2000000000 : ℝ)|^4475 ≤ (2157932349011/20000000000000 : ℝ)^3451
        have hw : |(-359179519/2000000000 : ℝ)|=(359179519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s4_7 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280620263/10000000000 : ℝ)*x 0 + (4530563023/10000000000 : ℝ)*x 1 + (2021418659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280620263/10000000000 : ℝ)^4475 ≤ (33278620346773/100000000000000 : ℝ)^3451 := by
    have hnat : (4280620263 : ℕ)^4475*100000000000000^3451 ≤ 33278620346773^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280620263 10000000000 33278620346773 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4530563023/10000000000 : ℝ)^4475 ≤ (7163969437907/20000000000000 : ℝ)^3451 := by
    have hnat : (4530563023 : ℕ)^4475*20000000000000^3451 ≤ 7163969437907^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530563023 10000000000 7163969437907 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021418659/5000000000 : ℝ)^4475 ≤ (30901532456197/100000000000000 : ℝ)^3451 := by
    have hnat : (2021418659 : ℕ)^4475*100000000000000^3451 ≤ 30901532456197^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021418659 5000000000 30901532456197 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280620263/10000000000 : ℝ), (4530563023/10000000000 : ℝ), (2021418659/5000000000 : ℝ)] ![(33278620346773/100000000000000 : ℝ), (7163969437907/20000000000000 : ℝ), (30901532456197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280620263/10000000000 : ℝ)|^4475 ≤ (33278620346773/100000000000000 : ℝ)^3451
        have hw : |(4280620263/10000000000 : ℝ)|=(4280620263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4530563023/10000000000 : ℝ)|^4475 ≤ (7163969437907/20000000000000 : ℝ)^3451
        have hw : |(4530563023/10000000000 : ℝ)|=(4530563023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2021418659/5000000000 : ℝ)|^4475 ≤ (30901532456197/100000000000000 : ℝ)^3451
        have hw : |(2021418659/5000000000 : ℝ)|=(2021418659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1489_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7783/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10813/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7783/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7783/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5371/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7783/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7783/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5371/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7783/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7783/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5371/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5371/50000 : ℝ) ^ (4473/1024 : ℝ) ≤ (1171253656498063/20000000000000000000 : ℝ) := by
    have hpowers : (5371/50000 : ℝ)^4473 ≤ (1171253656498063/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5371 : ℕ)^4473*20000000000000000000^1024 ≤ 1171253656498063^1024*50000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5371 50000 1171253656498063 20000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5371/50000 : ℝ)) (X := (1171253656498063/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7783/50000 : ℝ) ^ (4473/1024 : ℝ) ≤ (1184013646499263/4000000000000000000 : ℝ) := by
    have hpowers : (7783/50000 : ℝ)^4473 ≤ (1184013646499263/4000000000000000000 : ℝ)^1024 := by
      have hnat : (7783 : ℕ)^4473*4000000000000000000^1024 ≤ 1184013646499263^1024*50000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7783 50000 1184013646499263 4000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7783/50000 : ℝ)) (X := (1184013646499263/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001171253656498063/10000000000000000000 : ℝ) ≤ (625016757623373/625000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (10001171253656498063/10000000000000000000 : ℝ)^1024 ≤ (625016757623373/625000000000000 : ℝ)^4473 := by
      have hnat : (10001171253656498063 : ℕ)^1024*625000000000000^4473 ≤ 625016757623373^4473*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001171253656498063 10000000000000000000 625016757623373 625000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625016757623373/625000000000000 : ℝ)) (X := (10001171253656498063/10000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003545660944497189/10000000000000000000 : ℝ) ≤ (10000811594141423/10000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (10003545660944497189/10000000000000000000 : ℝ)^1024 ≤ (10000811594141423/10000000000000000 : ℝ)^4473 := by
      have hnat : (10003545660944497189 : ℕ)^1024*10000000000000000^4473 ≤ 10000811594141423^4473*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003545660944497189 10000000000000000000 10000811594141423 10000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000811594141423/10000000000000000 : ℝ)) (X := (10003545660944497189/10000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2001184013646499263/2000000000000000000 : ℝ) ≤ (5000677533154439/5000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (2001184013646499263/2000000000000000000 : ℝ)^1024 ≤ (5000677533154439/5000000000000000 : ℝ)^4473 := by
      have hnat : (2001184013646499263 : ℕ)^1024*5000000000000000^4473 ≤ 5000677533154439^4473*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2001184013646499263 2000000000000000000 5000677533154439 5000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000677533154439/5000000000000000 : ℝ)) (X := (2001184013646499263/2000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1171253656498063/20000000000000000000 : ℝ) ≤ ((12057404366089204603/12060000000000000000 : ℝ)+2*(108694433491/96480000000000 : ℝ)*(5371/50000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (12057404366089204603/12060000000000000000 : ℝ)+2*(108694433491/96480000000000 : ℝ)*(5371/50000 : ℝ)=(625016757623373/625000000000000 : ℝ) by norm_num, show 1+2*(1171253656498063/20000000000000000000 : ℝ)=(10001171253656498063/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1184013646499263/4000000000000000000 : ℝ)+(1171253656498063/20000000000000000000 : ℝ) ≤ ((12057404366089204603/12060000000000000000 : ℝ)+(108694433491/96480000000000 : ℝ)*((7783/50000 : ℝ)+(5371/50000 : ℝ)))^(4473/1024 : ℝ) := by
    rw [show (12057404366089204603/12060000000000000000 : ℝ)+(108694433491/96480000000000 : ℝ)*((7783/50000 : ℝ)+(5371/50000 : ℝ))=(10000811594141423/10000000000000000 : ℝ) by norm_num, show 1+(1184013646499263/4000000000000000000 : ℝ)+(1171253656498063/20000000000000000000 : ℝ)=(10003545660944497189/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1184013646499263/4000000000000000000 : ℝ) ≤ ((12057404366089204603/12060000000000000000 : ℝ)+2*(108694433491/96480000000000 : ℝ)*(7783/50000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (12057404366089204603/12060000000000000000 : ℝ)+2*(108694433491/96480000000000 : ℝ)*(7783/50000 : ℝ)=(5000677533154439/5000000000000000 : ℝ) by norm_num, show 1+2*(1184013646499263/4000000000000000000 : ℝ)=(2001184013646499263/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (12057404366089204603/12060000000000000000 : ℝ)*(X 1 0+X 2 0)+(108694433491/96480000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (7783/50000 : ℝ)) (c := (12057404366089204603/12060000000000000000 : ℝ)) (alpha := (108694433491/96480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (12057404366089204603/12060000000000000000 : ℝ)*(X 0 1+X 2 1)+(108694433491/96480000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (7783/50000 : ℝ)) (c := (12057404366089204603/12060000000000000000 : ℝ)) (alpha := (108694433491/96480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (12057404366089204603/12060000000000000000 : ℝ)*(X 0 2+X 1 2)+(108694433491/96480000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (5371/50000 : ℝ)) (hi := (7783/50000 : ℝ)) (c := (12057404366089204603/12060000000000000000 : ℝ)) (alpha := (108694433491/96480000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-951227057/5000000000 : ℝ)*X 0 0+(5436796579/10000000000 : ℝ)*X 0 1+(5215888283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535298247/1000000000 : ℝ)*X 1 0+(-2015659227/10000000000 : ℝ)*X 1 1+(5215888853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352982577/10000000000 : ℝ)*X 2 0+(1043177687/2000000000 : ℝ)*X 2 1+(-2015659639/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((428055329/1000000000 : ℝ)*X 0 0+(4040280867/10000000000 : ℝ)*X 0 1+(4533099929/10000000000 : ℝ)*X 0 2+(428055329/1000000000 : ℝ)*X 1 0+(4040280867/10000000000 : ℝ)*X 1 1+(4533099929/10000000000 : ℝ)*X 1 2+(428055329/1000000000 : ℝ)*X 2 0+(4040280867/10000000000 : ℝ)*X 2 1+(4533099929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-190248449/1000000000 : ℝ)*X 0 0+(5217025997/10000000000 : ℝ)*X 0 1+(5435650467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132380047/250000000 : ℝ)*X 1 0+(-1795897587/10000000000 : ℝ)*X 1 1+(5435650463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295201863/10000000000 : ℝ)*X 2 0+(2717825237/5000000000 : ℝ)*X 2 1+(-359179519/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4280620263/10000000000 : ℝ)*X 0 0+(4530563023/10000000000 : ℝ)*X 0 1+(2021418659/5000000000 : ℝ)*X 0 2+(4280620263/10000000000 : ℝ)*X 1 0+(4530563023/10000000000 : ℝ)*X 1 1+(2021418659/5000000000 : ℝ)*X 1 2+(4280620263/10000000000 : ℝ)*X 2 0+(4530563023/10000000000 : ℝ)*X 2 1+(2021418659/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (207297082054425407163/26800000000000000000000000 : ℝ) := by norm_num
    linear_combination (207238351/12500000000000 : ℝ)*(base19) + (198516403/12500000000000 : ℝ)*(base23) + (148109483/100000000000000 : ℝ)*(lower2) + (490272967/100000000000000 : ℝ)*(upper3) + (62321691/100000000000000 : ℝ)*(lower4) + (819499057607421/25000000000000 : ℝ)*(major0) + (819499057607421/25000000000000 : ℝ)*(major1) + (819499057607421/25000000000000 : ℝ)*(major2) + (4526802636855297/100000000000000 : ℝ)*(sp0) + (565853312847433/12500000000000 : ℝ)*(sp1) + (4526826572555049/100000000000000 : ℝ)*(sp2) + (6341094234807/312500000000 : ℝ)*(sp3) + (398809859/1562500000000 : ℝ)*(sp4) + (3471800663/25000000000000 : ℝ)*(sp7) + (507291010585223/25000000000000 : ℝ)*(f.failure) + (70731690010723/1562500000000 : ℝ)*(f.sum) + (912491145027/134000000000000000000000000 : ℝ)*base65 + (13078898973051793/33500000000000000000000000000000 : ℝ)*base68 + (391531749911051793/33500000000000000000000000000000 : ℝ)*base70 + (345617659519448207/33500000000000000000000000000000 : ℝ)*base71 + (113900219847/134000000000000000000000000 : ℝ)*base73 + (349399007797448207/33500000000000000000000000000000 : ℝ)*base75 + (124437755553948207/33500000000000000000000000000000 : ℝ)*base77 + (200894849353051793/33500000000000000000000000000000 : ℝ)*base80 + (331608916089/134000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (25614867/2500000000000000000000 : ℝ)*base90 + (25614867/2500000000000000000000 : ℝ)*base92 + (25614867/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (168025589307015878104040837/33500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (824251131/100000000000000 : ℝ)*(base19) + (109860603/12500000000000 : ℝ)*(base23) + (5098933/5000000000000 : ℝ)*(upper3) + (16202187/50000000000000 : ℝ)*(lower4) + (5094313/5000000000000 : ℝ)*(upper5) + (1656096377587437/50000000000000 : ℝ)*(major0) + (1656096377587437/50000000000000 : ℝ)*(major1) + (1656096377587437/50000000000000 : ℝ)*(major2) + (6197823783/50000000000000 : ℝ)*(sp1) + (328500351/2500000000000 : ℝ)*(sp2) + (4574052771782533/100000000000000 : ℝ)*(sp4) + (914807910376767/20000000000000 : ℝ)*(sp5) + (4574038752883669/100000000000000 : ℝ)*(sp6) + (2050332571377567/100000000000000 : ℝ)*(sp7) + (2050332571377567/100000000000000 : ℝ)*(f.failure) + (4574052771782533/100000000000000 : ℝ)*(f.sum) + (187963476883/160800000000000000000000000 : ℝ)*base66 + (324052784717805279/67000000000000000000000000000000 : ℝ)*base67 + (274721041207194721/67000000000000000000000000000000 : ℝ)*base70 + (955392782715194721/67000000000000000000000000000000 : ℝ)*base72 + (4563819523333/804000000000000000000000000 : ℝ)*base73 + (694631307828805279/67000000000000000000000000000000 : ℝ)*base75 + (462050249384194721/67000000000000000000000000000000 : ℝ)*base78 + (248718564317194721/67000000000000000000000000000000 : ℝ)*base80 + (3181187231/1286400000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (10988043/10000000000000000000000 : ℝ)*base90 + (10988043/10000000000000000000000 : ℝ)*base92 + (10988043/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1489_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7783/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5371/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10813/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1489_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1489_s5_0 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-380505851/2000000000 : ℝ)*x 0 + (2718152759/5000000000 : ℝ)*x 1 + (2608164853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (380505851/2000000000 : ℝ)^4475 ≤ (11627611523753/100000000000000 : ℝ)^3451 := by
    have hnat : (380505851 : ℕ)^4475*100000000000000^3451 ≤ 11627611523753^3451*2000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      380505851 2000000000 11627611523753 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2718152759/5000000000 : ℝ)^4475 ≤ (45369264336609/100000000000000 : ℝ)^3451 := by
    have hnat : (2718152759 : ℕ)^4475*100000000000000^3451 ≤ 45369264336609^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718152759 5000000000 45369264336609 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608164853/5000000000 : ℝ)^4475 ≤ (43003124120269/100000000000000 : ℝ)^3451 := by
    have hnat : (2608164853 : ℕ)^4475*100000000000000^3451 ≤ 43003124120269^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608164853 5000000000 43003124120269 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-380505851/2000000000 : ℝ), (2718152759/5000000000 : ℝ), (2608164853/5000000000 : ℝ)] ![(11627611523753/100000000000000 : ℝ), (45369264336609/100000000000000 : ℝ), (43003124120269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-380505851/2000000000 : ℝ)|^4475 ≤ (11627611523753/100000000000000 : ℝ)^3451
        have hw : |(-380505851/2000000000 : ℝ)|=(380505851/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2718152759/5000000000 : ℝ)|^4475 ≤ (45369264336609/100000000000000 : ℝ)^3451
        have hw : |(2718152759/5000000000 : ℝ)|=(2718152759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608164853/5000000000 : ℝ)|^4475 ≤ (43003124120269/100000000000000 : ℝ)^3451
        have hw : |(2608164853/5000000000 : ℝ)|=(2608164853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s5_1 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267642729/500000000 : ℝ)*x 0 + (-1007622747/5000000000 : ℝ)*x 1 + (1304082437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267642729/500000000 : ℝ)^4475 ≤ (22234112892207/50000000000000 : ℝ)^3451 := by
    have hnat : (267642729 : ℕ)^4475*50000000000000^3451 ≤ 22234112892207^3451*500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267642729 500000000 22234112892207 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1007622747/5000000000 : ℝ)^4475 ≤ (6264324814603/50000000000000 : ℝ)^3451 := by
    have hnat : (1007622747 : ℕ)^4475*50000000000000^3451 ≤ 6264324814603^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007622747 5000000000 6264324814603 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304082437/2500000000 : ℝ)^4475 ≤ (8600624913851/20000000000000 : ℝ)^3451 := by
    have hnat : (1304082437 : ℕ)^4475*20000000000000^3451 ≤ 8600624913851^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304082437 2500000000 8600624913851 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267642729/500000000 : ℝ), (-1007622747/5000000000 : ℝ), (1304082437/2500000000 : ℝ)] ![(22234112892207/50000000000000 : ℝ), (6264324814603/50000000000000 : ℝ), (8600624913851/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267642729/500000000 : ℝ)|^4475 ≤ (22234112892207/50000000000000 : ℝ)^3451
        have hw : |(267642729/500000000 : ℝ)|=(267642729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1007622747/5000000000 : ℝ)|^4475 ≤ (6264324814603/50000000000000 : ℝ)^3451
        have hw : |(-1007622747/5000000000 : ℝ)|=(1007622747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304082437/2500000000 : ℝ)|^4475 ≤ (8600624913851/20000000000000 : ℝ)^3451
        have hw : |(1304082437/2500000000 : ℝ)|=(1304082437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s5_2 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338213631/2500000000 : ℝ)*x 0 + (5216329777/10000000000 : ℝ)*x 1 + (-2015245531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338213631/2500000000 : ℝ)^4475 ≤ (44468225181159/100000000000000 : ℝ)^3451 := by
    have hnat : (1338213631 : ℕ)^4475*100000000000000^3451 ≤ 44468225181159^3451*2500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338213631 2500000000 44468225181159 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216329777/10000000000 : ℝ)^4475 ≤ (43003124879269/100000000000000 : ℝ)^3451 := by
    have hnat : (5216329777 : ℕ)^4475*100000000000000^3451 ≤ 43003124879269^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216329777 10000000000 43003124879269 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015245531/10000000000 : ℝ)^4475 ≤ (12528649927487/100000000000000 : ℝ)^3451 := by
    have hnat : (2015245531 : ℕ)^4475*100000000000000^3451 ≤ 12528649927487^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015245531 10000000000 12528649927487 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338213631/2500000000 : ℝ), (5216329777/10000000000 : ℝ), (-2015245531/10000000000 : ℝ)] ![(44468225181159/100000000000000 : ℝ), (43003124879269/100000000000000 : ℝ), (12528649927487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338213631/2500000000 : ℝ)|^4475 ≤ (44468225181159/100000000000000 : ℝ)^3451
        have hw : |(1338213631/2500000000 : ℝ)|=(1338213631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216329777/10000000000 : ℝ)|^4475 ≤ (43003124879269/100000000000000 : ℝ)^3451
        have hw : |(5216329777/10000000000 : ℝ)|=(5216329777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015245531/10000000000 : ℝ)|^4475 ≤ (12528649927487/100000000000000 : ℝ)^3451
        have hw : |(-2015245531/10000000000 : ℝ)|=(2015245531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s5_3 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280598767/10000000000 : ℝ)*x 0 + (404131517/1000000000 : ℝ)*x 1 + (283253473/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280598767/10000000000 : ℝ)^4475 ≤ (33278403644223/100000000000000 : ℝ)^3451 := by
    have hnat : (4280598767 : ℕ)^4475*100000000000000^3451 ≤ 33278403644223^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280598767 10000000000 33278403644223 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404131517/1000000000 : ℝ)^4475 ≤ (30886446444123/100000000000000 : ℝ)^3451 := by
    have hnat : (404131517 : ℕ)^4475*100000000000000^3451 ≤ 30886446444123^3451*1000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404131517 1000000000 30886446444123 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283253473/625000000 : ℝ)^4475 ≤ (7167029979509/20000000000000 : ℝ)^3451 := by
    have hnat : (283253473 : ℕ)^4475*20000000000000^3451 ≤ 7167029979509^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283253473 625000000 7167029979509 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280598767/10000000000 : ℝ), (404131517/1000000000 : ℝ), (283253473/625000000 : ℝ)] ![(33278403644223/100000000000000 : ℝ), (30886446444123/100000000000000 : ℝ), (7167029979509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280598767/10000000000 : ℝ)|^4475 ≤ (33278403644223/100000000000000 : ℝ)^3451
        have hw : |(4280598767/10000000000 : ℝ)|=(4280598767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(404131517/1000000000 : ℝ)|^4475 ≤ (30886446444123/100000000000000 : ℝ)^3451
        have hw : |(404131517/1000000000 : ℝ)|=(404131517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283253473/625000000 : ℝ)|^4475 ≤ (7167029979509/20000000000000 : ℝ)^3451
        have hw : |(283253473/625000000 : ℝ)|=(283253473/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s5_4 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1902559287/10000000000 : ℝ)*x 0 + (5217457641/10000000000 : ℝ)*x 1 + (271758463/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1902559287/10000000000 : ℝ)^4475 ≤ (2906962383071/25000000000000 : ℝ)^3451 := by
    have hnat : (1902559287 : ℕ)^4475*25000000000000^3451 ≤ 2906962383071^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1902559287 10000000000 2906962383071 25000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217457641/10000000000 : ℝ)^4475 ≤ (4301518228073/10000000000000 : ℝ)^3451 := by
    have hnat : (5217457641 : ℕ)^4475*10000000000000^3451 ≤ 4301518228073^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217457641 10000000000 4301518228073 10000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271758463/500000000 : ℝ)^4475 ≤ (22678484089129/50000000000000 : ℝ)^3451 := by
    have hnat : (271758463 : ℕ)^4475*50000000000000^3451 ≤ 22678484089129^3451*500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271758463 500000000 22678484089129 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1902559287/10000000000 : ℝ), (5217457641/10000000000 : ℝ), (271758463/500000000 : ℝ)] ![(2906962383071/25000000000000 : ℝ), (4301518228073/10000000000000 : ℝ), (22678484089129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1902559287/10000000000 : ℝ)|^4475 ≤ (2906962383071/25000000000000 : ℝ)^3451
        have hw : |(-1902559287/10000000000 : ℝ)|=(1902559287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217457641/10000000000 : ℝ)|^4475 ≤ (4301518228073/10000000000000 : ℝ)^3451
        have hw : |(5217457641/10000000000 : ℝ)|=(5217457641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271758463/500000000 : ℝ)|^4475 ≤ (22678484089129/50000000000000 : ℝ)^3451
        have hw : |(271758463/500000000 : ℝ)|=(271758463/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s5_5 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330957371/625000000 : ℝ)*x 0 + (-1796405983/10000000000 : ℝ)*x 1 + (5435169279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330957371/625000000 : ℝ)^4475 ≤ (43849409009979/100000000000000 : ℝ)^3451 := by
    have hnat : (330957371 : ℕ)^4475*100000000000000^3451 ≤ 43849409009979^3451*625000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330957371 625000000 43849409009979 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1796405983/10000000000 : ℝ)^4475 ≤ (2158724518053/20000000000000 : ℝ)^3451 := by
    have hnat : (1796405983 : ℕ)^4475*20000000000000^3451 ≤ 2158724518053^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796405983 10000000000 2158724518053 20000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5435169279/10000000000 : ℝ)^4475 ≤ (22678484191931/50000000000000 : ℝ)^3451 := by
    have hnat : (5435169279 : ℕ)^4475*50000000000000^3451 ≤ 22678484191931^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435169279 10000000000 22678484191931 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330957371/625000000 : ℝ), (-1796405983/10000000000 : ℝ), (5435169279/10000000000 : ℝ)] ![(43849409009979/100000000000000 : ℝ), (2158724518053/20000000000000 : ℝ), (22678484191931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330957371/625000000 : ℝ)|^4475 ≤ (43849409009979/100000000000000 : ℝ)^3451
        have hw : |(330957371/625000000 : ℝ)|=(330957371/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1796405983/10000000000 : ℝ)|^4475 ≤ (2158724518053/20000000000000 : ℝ)^3451
        have hw : |(-1796405983/10000000000 : ℝ)|=(1796405983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5435169279/10000000000 : ℝ)|^4475 ≤ (22678484191931/50000000000000 : ℝ)^3451
        have hw : |(5435169279/10000000000 : ℝ)|=(5435169279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s5_6 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647658971/5000000000 : ℝ)*x 0 + (2717584639/5000000000 : ℝ)*x 1 + (-224550747/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647658971/5000000000 : ℝ)^4475 ≤ (21924704537203/50000000000000 : ℝ)^3451 := by
    have hnat : (2647658971 : ℕ)^4475*50000000000000^3451 ≤ 21924704537203^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647658971 5000000000 21924704537203 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717584639/5000000000 : ℝ)^4475 ≤ (45356968373041/100000000000000 : ℝ)^3451 := by
    have hnat : (2717584639 : ℕ)^4475*100000000000000^3451 ≤ 45356968373041^3451*5000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717584639 5000000000 45356968373041 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224550747/1250000000 : ℝ)^4475 ≤ (5396811267863/50000000000000 : ℝ)^3451 := by
    have hnat : (224550747 : ℕ)^4475*50000000000000^3451 ≤ 5396811267863^3451*1250000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224550747 1250000000 5396811267863 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647658971/5000000000 : ℝ), (2717584639/5000000000 : ℝ), (-224550747/1250000000 : ℝ)] ![(21924704537203/50000000000000 : ℝ), (45356968373041/100000000000000 : ℝ), (5396811267863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647658971/5000000000 : ℝ)|^4475 ≤ (21924704537203/50000000000000 : ℝ)^3451
        have hw : |(2647658971/5000000000 : ℝ)|=(2647658971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717584639/5000000000 : ℝ)|^4475 ≤ (45356968373041/100000000000000 : ℝ)^3451
        have hw : |(2717584639/5000000000 : ℝ)|=(2717584639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224550747/1250000000 : ℝ)|^4475 ≤ (5396811267863/50000000000000 : ℝ)^3451
        have hw : |(-224550747/1250000000 : ℝ)|=(224550747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1489_s5_7 (p : ℝ) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4280665621/10000000000 : ℝ)*x 0 + (4529539303/10000000000 : ℝ)*x 1 + (202192501/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4280665621/10000000000 : ℝ)^4475 ≤ (4159884700591/12500000000000 : ℝ)^3451 := by
    have hnat : (4280665621 : ℕ)^4475*12500000000000^3451 ≤ 4159884700591^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4280665621 10000000000 4159884700591 12500000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4529539303/10000000000 : ℝ)^4475 ≤ (35809352097273/100000000000000 : ℝ)^3451 := by
    have hnat : (4529539303 : ℕ)^4475*100000000000000^3451 ≤ 35809352097273^3451*10000000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4529539303 10000000000 35809352097273 100000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202192501/500000000 : ℝ)^4475 ≤ (15455785140811/50000000000000 : ℝ)^3451 := by
    have hnat : (202192501 : ℕ)^4475*50000000000000^3451 ≤ 15455785140811^3451*500000000^4475 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202192501 500000000 15455785140811 50000000000000 4475 3451 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4475/1024 : ℝ)) 4475 3451 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4280665621/10000000000 : ℝ), (4529539303/10000000000 : ℝ), (202192501/500000000 : ℝ)] ![(4159884700591/12500000000000 : ℝ), (35809352097273/100000000000000 : ℝ), (15455785140811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4280665621/10000000000 : ℝ)|^4475 ≤ (4159884700591/12500000000000 : ℝ)^3451
        have hw : |(4280665621/10000000000 : ℝ)|=(4280665621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4529539303/10000000000 : ℝ)|^4475 ≤ (35809352097273/100000000000000 : ℝ)^3451
        have hw : |(4529539303/10000000000 : ℝ)|=(4529539303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(202192501/500000000 : ℝ)|^4475 ≤ (15455785140811/50000000000000 : ℝ)^3451
        have hw : |(202192501/500000000 : ℝ)|=(202192501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1489_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10813/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10823/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15479/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10813/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10813/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10813/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10813/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10813/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10813/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10813/100000 : ℝ) ^ (4473/1024 : ℝ) ≤ (602724050490069/10000000000000000000 : ℝ) := by
    have hpowers : (10813/100000 : ℝ)^4473 ≤ (602724050490069/10000000000000000000 : ℝ)^1024 := by
      have hnat : (10813 : ℕ)^4473*10000000000000000000^1024 ≤ 602724050490069^1024*100000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10813 100000 602724050490069 10000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10813/100000 : ℝ)) (X := (602724050490069/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4473/1024 : ℝ) ≤ (7241511833476741/25000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4473 ≤ (7241511833476741/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4473*25000000000000000000^1024 ≤ 7241511833476741^1024*100000^4473 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 7241511833476741 25000000000000000000 4473 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (7241511833476741/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000602724050490069/5000000000000000000 : ℝ) ≤ (10000275949361189/10000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (5000602724050490069/5000000000000000000 : ℝ)^1024 ≤ (10000275949361189/10000000000000000 : ℝ)^4473 := by
      have hnat : (5000602724050490069 : ℕ)^1024*10000000000000000^4473 ≤ 10000275949361189^4473*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000602724050490069 5000000000000000000 10000275949361189 10000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000275949361189/10000000000000000 : ℝ)) (X := (5000602724050490069/5000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017496643919403827/50000000000000000000 : ℝ) ≤ (10000800990240189/10000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (50017496643919403827/50000000000000000000 : ℝ)^1024 ≤ (10000800990240189/10000000000000000 : ℝ)^4473 := by
      have hnat : (50017496643919403827 : ℕ)^1024*10000000000000000^4473 ≤ 10000800990240189^4473*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017496643919403827 50000000000000000000 10000800990240189 10000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000800990240189/10000000000000000 : ℝ)) (X := (50017496643919403827/50000000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507241511833476741/12500000000000000000 : ℝ) ≤ (10001326031119189/10000000000000000 : ℝ) ^ (4473/1024 : ℝ) := by
    have hpowers : (12507241511833476741/12500000000000000000 : ℝ)^1024 ≤ (10001326031119189/10000000000000000 : ℝ)^4473 := by
      have hnat : (12507241511833476741 : ℕ)^1024*10000000000000000^4473 ≤ 10001326031119189^4473*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507241511833476741 12500000000000000000 10001326031119189 10000000000000000 1024 4473 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001326031119189/10000000000000000 : ℝ)) (X := (12507241511833476741/12500000000000000000 : ℝ)) (by norm_num) 4473 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(602724050490069/10000000000000000000 : ℝ) ≤ ((11687483951290916441/11690000000000000000 : ℝ)+2*(525040879/467600000000 : ℝ)*(10813/100000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (11687483951290916441/11690000000000000000 : ℝ)+2*(525040879/467600000000 : ℝ)*(10813/100000 : ℝ)=(10000275949361189/10000000000000000 : ℝ) by norm_num, show 1+2*(602724050490069/10000000000000000000 : ℝ)=(5000602724050490069/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7241511833476741/25000000000000000000 : ℝ)+(602724050490069/10000000000000000000 : ℝ) ≤ ((11687483951290916441/11690000000000000000 : ℝ)+(525040879/467600000000 : ℝ)*((15489/100000 : ℝ)+(10813/100000 : ℝ)))^(4473/1024 : ℝ) := by
    rw [show (11687483951290916441/11690000000000000000 : ℝ)+(525040879/467600000000 : ℝ)*((15489/100000 : ℝ)+(10813/100000 : ℝ))=(10000800990240189/10000000000000000 : ℝ) by norm_num, show 1+(7241511833476741/25000000000000000000 : ℝ)+(602724050490069/10000000000000000000 : ℝ)=(50017496643919403827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7241511833476741/25000000000000000000 : ℝ) ≤ ((11687483951290916441/11690000000000000000 : ℝ)+2*(525040879/467600000000 : ℝ)*(15489/100000 : ℝ))^(4473/1024 : ℝ) := by
    rw [show (11687483951290916441/11690000000000000000 : ℝ)+2*(525040879/467600000000 : ℝ)*(15489/100000 : ℝ)=(10001326031119189/10000000000000000 : ℝ) by norm_num, show 1+2*(7241511833476741/25000000000000000000 : ℝ)=(12507241511833476741/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11687483951290916441/11690000000000000000 : ℝ)*(X 1 0+X 2 0)+(525040879/467600000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10813/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (11687483951290916441/11690000000000000000 : ℝ)) (alpha := (525040879/467600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11687483951290916441/11690000000000000000 : ℝ)*(X 0 1+X 2 1)+(525040879/467600000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10813/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (11687483951290916441/11690000000000000000 : ℝ)) (alpha := (525040879/467600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11687483951290916441/11690000000000000000 : ℝ)*(X 0 2+X 1 2)+(525040879/467600000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4473/1024 : ℝ)) (lo := (10813/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (11687483951290916441/11690000000000000000 : ℝ)) (alpha := (525040879/467600000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-380505851/2000000000 : ℝ)*X 0 0+(2718152759/5000000000 : ℝ)*X 0 1+(2608164853/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267642729/500000000 : ℝ)*X 1 0+(-1007622747/5000000000 : ℝ)*X 1 1+(1304082437/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338213631/2500000000 : ℝ)*X 2 0+(5216329777/10000000000 : ℝ)*X 2 1+(-2015245531/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4280598767/10000000000 : ℝ)*X 0 0+(404131517/1000000000 : ℝ)*X 0 1+(283253473/625000000 : ℝ)*X 0 2+(4280598767/10000000000 : ℝ)*X 1 0+(404131517/1000000000 : ℝ)*X 1 1+(283253473/625000000 : ℝ)*X 1 2+(4280598767/10000000000 : ℝ)*X 2 0+(404131517/1000000000 : ℝ)*X 2 1+(283253473/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1902559287/10000000000 : ℝ)*X 0 0+(5217457641/10000000000 : ℝ)*X 0 1+(271758463/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330957371/625000000 : ℝ)*X 1 0+(-1796405983/10000000000 : ℝ)*X 1 1+(5435169279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647658971/5000000000 : ℝ)*X 2 0+(2717584639/5000000000 : ℝ)*X 2 1+(-224550747/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4280665621/10000000000 : ℝ)*X 0 0+(4529539303/10000000000 : ℝ)*X 0 1+(202192501/500000000 : ℝ)*X 0 2+(4280665621/10000000000 : ℝ)*X 1 0+(4529539303/10000000000 : ℝ)*X 1 1+(202192501/500000000 : ℝ)*X 1 2+(4280665621/10000000000 : ℝ)*X 2 0+(4529539303/10000000000 : ℝ)*X 2 1+(202192501/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1489_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (438176081904040172619929031/146125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104715209/20000000000000 : ℝ)*(base19) + (408986723/100000000000000 : ℝ)*(base23) + (448507/1250000000000 : ℝ)*(lower2) + (108657779/100000000000000 : ℝ)*(upper3) + (8379057/50000000000000 : ℝ)*(upper5) + (1645929072748997/50000000000000 : ℝ)*(major0) + (1645929072748997/50000000000000 : ℝ)*(major1) + (1645929072748997/50000000000000 : ℝ)*(major2) + (454596391419409/10000000000000 : ℝ)*(sp0) + (2272985371445549/50000000000000 : ℝ)*(sp1) + (227298542874021/5000000000000 : ℝ)*(sp2) + (127358784137269/6250000000000 : ℝ)*(sp3) + (7352273053/100000000000000 : ℝ)*(sp4) + (4378377913/100000000000000 : ℝ)*(sp7) + (2037744924574217/100000000000000 : ℝ)*(f.failure) + (4545971266467143/100000000000000 : ℝ)*(f.sum) + (85255766879/14612500000000000000000000 : ℝ)*base66 + (2460044637695440323/584500000000000000000000000000000 : ℝ)*base68 + (2669841759425440323/584500000000000000000000000000000 : ℝ)*base70 + (143416517974059677/584500000000000000000000000000000 : ℝ)*base71 + (8980123300983/1169000000000000000000000000 : ℝ)*base74 + (1800804227573440323/584500000000000000000000000000000 : ℝ)*base76 + (5156765911805940323/584500000000000000000000000000000 : ℝ)*base78 + (1850545424816940323/584500000000000000000000000000000 : ℝ)*base80 + (1016204913707/292250000000000000000000000 : ℝ)*base82 + (13239107/10000000000000000000000 : ℝ)*base89 + (13239107/10000000000000000000000 : ℝ)*base91 + (13239107/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2177672875306173492781191291/292250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1220839639/100000000000000 : ℝ)*(base19) + (1306676209/100000000000000 : ℝ)*(base23) + (158686239/100000000000000 : ℝ)*(upper3) + (34661633/100000000000000 : ℝ)*(lower4) + (29958311/20000000000000 : ℝ)*(upper5) + (3326080515933617/100000000000000 : ℝ)*(major0) + (3326080515933617/100000000000000 : ℝ)*(major1) + (3326080515933617/100000000000000 : ℝ)*(major2) + (4653335811/25000000000000 : ℝ)*(sp1) + (5002493531/25000000000000 : ℝ)*(sp2) + (91864626614571/2000000000000 : ℝ)*(sp4) + (2296605748272833/50000000000000 : ℝ)*(sp5) + (4593210014078217/100000000000000 : ℝ)*(sp6) + (1029464726379269/50000000000000 : ℝ)*(sp7) + (1029464726379269/50000000000000 : ℝ)*(f.failure) + (91864626614571/2000000000000 : ℝ)*(f.sum) + (579723402381/584500000000000000000000000 : ℝ)*base66 + (4101285468091102903/1169000000000000000000000000000000 : ℝ)*base68 + (4320092103215102903/1169000000000000000000000000000000 : ℝ)*base70 + (6268699645761102903/1169000000000000000000000000000000 : ℝ)*base72 + (100582947359/23380000000000000000000000 : ℝ)*base73 + (14955029479690897097/1169000000000000000000000000000000 : ℝ)*base75 + (6125477850247102903/1169000000000000000000000000000000 : ℝ)*base78 + (5566927546047102903/1169000000000000000000000000000000 : ℝ)*base80 + (2326803454097/584500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7809001/5000000000000000000000 : ℝ)*base90 + (7809001/5000000000000000000000 : ℝ)*base92 + (7809001/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1489_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10813/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10823/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1489_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1489_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1609/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10823/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1489_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1489_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1489_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4473/1024 : ℝ) ≤ p) (hpb : p ≤ (4475/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (161544171/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1609/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10823/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15479/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1489_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
