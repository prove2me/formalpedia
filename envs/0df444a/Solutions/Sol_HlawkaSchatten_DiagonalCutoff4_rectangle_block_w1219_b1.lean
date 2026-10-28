-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1219_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:10:27.465792+00:00
-- url     : https://prove2.me/submissions/0a3ec58f-3fc8-4963-98c6-101709933c48

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
theorem support_rectangle_w1219_s3_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1063778099/5000000000 : ℝ)*x 0 + (271085511/500000000 : ℝ)*x 1 + (2619404221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1063778099/5000000000 : ℝ)^2103 ≤ (6464818253327/50000000000000 : ℝ)^1591 := by
    have hnat : (1063778099 : ℕ)^2103*50000000000000^1591 ≤ 6464818253327^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063778099 5000000000 6464818253327 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (271085511/500000000 : ℝ)^2103 ≤ (44522409154939/100000000000000 : ℝ)^1591 := by
    have hnat : (271085511 : ℕ)^2103*100000000000000^1591 ≤ 44522409154939^1591*500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271085511 500000000 44522409154939 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2619404221/5000000000 : ℝ)^2103 ≤ (42547954323337/100000000000000 : ℝ)^1591 := by
    have hnat : (2619404221 : ℕ)^2103*100000000000000^1591 ≤ 42547954323337^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619404221 5000000000 42547954323337 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1063778099/5000000000 : ℝ), (271085511/500000000 : ℝ), (2619404221/5000000000 : ℝ)] ![(6464818253327/50000000000000 : ℝ), (44522409154939/100000000000000 : ℝ), (42547954323337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1063778099/5000000000 : ℝ)|^2103 ≤ (6464818253327/50000000000000 : ℝ)^1591
        have hw : |(-1063778099/5000000000 : ℝ)|=(1063778099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(271085511/500000000 : ℝ)|^2103 ≤ (44522409154939/100000000000000 : ℝ)^1591
        have hw : |(271085511/500000000 : ℝ)|=(271085511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2619404221/5000000000 : ℝ)|^2103 ≤ (42547954323337/100000000000000 : ℝ)^1591
        have hw : |(2619404221/5000000000 : ℝ)|=(2619404221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s3_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676000963/5000000000 : ℝ)*x 0 + (-2220901557/10000000000 : ℝ)*x 1 + (1309702161/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676000963/5000000000 : ℝ)^2103 ≤ (43767327579937/100000000000000 : ℝ)^1591 := by
    have hnat : (2676000963 : ℕ)^2103*100000000000000^1591 ≤ 43767327579937^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676000963 5000000000 43767327579937 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2220901557/10000000000 : ℝ)^2103 ≤ (2736943183359/20000000000000 : ℝ)^1591 := by
    have hnat : (2220901557 : ℕ)^2103*20000000000000^1591 ≤ 2736943183359^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2220901557 10000000000 2736943183359 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309702161/2500000000 : ℝ)^2103 ≤ (42547956491873/100000000000000 : ℝ)^1591 := by
    have hnat : (1309702161 : ℕ)^2103*100000000000000^1591 ≤ 42547956491873^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309702161 2500000000 42547956491873 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676000963/5000000000 : ℝ), (-2220901557/10000000000 : ℝ), (1309702161/2500000000 : ℝ)] ![(43767327579937/100000000000000 : ℝ), (2736943183359/20000000000000 : ℝ), (42547956491873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676000963/5000000000 : ℝ)|^2103 ≤ (43767327579937/100000000000000 : ℝ)^1591
        have hw : |(2676000963/5000000000 : ℝ)|=(2676000963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2220901557/10000000000 : ℝ)|^2103 ≤ (2736943183359/20000000000000 : ℝ)^1591
        have hw : |(-2220901557/10000000000 : ℝ)|=(2220901557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1309702161/2500000000 : ℝ)|^2103 ≤ (42547956491873/100000000000000 : ℝ)^1591
        have hw : |(1309702161/2500000000 : ℝ)|=(1309702161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s3_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2676000897/5000000000 : ℝ)*x 0 + (523880901/1000000000 : ℝ)*x 1 + (-1776721/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676000897/5000000000 : ℝ)^2103 ≤ (10941831538273/25000000000000 : ℝ)^1591 := by
    have hnat : (2676000897 : ℕ)^2103*25000000000000^1591 ≤ 10941831538273^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676000897 5000000000 10941831538273 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523880901/1000000000 : ℝ)^2103 ≤ (42547960421003/100000000000000 : ℝ)^1591 := by
    have hnat : (523880901 : ℕ)^2103*100000000000000^1591 ≤ 42547960421003^1591*1000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523880901 1000000000 42547960421003 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1776721/8000000 : ℝ)^2103 ≤ (13684713416369/100000000000000 : ℝ)^1591 := by
    have hnat : (1776721 : ℕ)^2103*100000000000000^1591 ≤ 13684713416369^1591*8000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1776721 8000000 13684713416369 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676000897/5000000000 : ℝ), (523880901/1000000000 : ℝ), (-1776721/8000000 : ℝ)] ![(10941831538273/25000000000000 : ℝ), (42547960421003/100000000000000 : ℝ), (13684713416369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676000897/5000000000 : ℝ)|^2103 ≤ (10941831538273/25000000000000 : ℝ)^1591
        have hw : |(2676000897/5000000000 : ℝ)|=(2676000897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523880901/1000000000 : ℝ)|^2103 ≤ (42547960421003/100000000000000 : ℝ)^1591
        have hw : |(523880901/1000000000 : ℝ)|=(523880901/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1776721/8000000 : ℝ)|^2103 ≤ (13684713416369/100000000000000 : ℝ)^1591
        have hw : |(-1776721/8000000 : ℝ)|=(1776721/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s3_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4352123763/10000000000 : ℝ)*x 0 + (2085629741/5000000000 : ℝ)*x 1 + (2270320287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352123763/10000000000 : ℝ)^2103 ≤ (166495162883/500000000000 : ℝ)^1591 := by
    have hnat : (4352123763 : ℕ)^2103*500000000000^1591 ≤ 166495162883^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352123763 10000000000 166495162883 500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2085629741/5000000000 : ℝ)^2103 ≤ (3148221840893/10000000000000 : ℝ)^1591 := by
    have hnat : (2085629741 : ℕ)^2103*10000000000000^1591 ≤ 3148221840893^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085629741 5000000000 3148221840893 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270320287/5000000000 : ℝ)^2103 ≤ (17609374494299/50000000000000 : ℝ)^1591 := by
    have hnat : (2270320287 : ℕ)^2103*50000000000000^1591 ≤ 17609374494299^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270320287 5000000000 17609374494299 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352123763/10000000000 : ℝ), (2085629741/5000000000 : ℝ), (2270320287/5000000000 : ℝ)] ![(166495162883/500000000000 : ℝ), (3148221840893/10000000000000 : ℝ), (17609374494299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352123763/10000000000 : ℝ)|^2103 ≤ (166495162883/500000000000 : ℝ)^1591
        have hw : |(4352123763/10000000000 : ℝ)|=(4352123763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2085629741/5000000000 : ℝ)|^2103 ≤ (3148221840893/10000000000000 : ℝ)^1591
        have hw : |(2085629741/5000000000 : ℝ)|=(2085629741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2270320287/5000000000 : ℝ)|^2103 ≤ (17609374494299/50000000000000 : ℝ)^1591
        have hw : |(2270320287/5000000000 : ℝ)|=(2270320287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s3_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-425514243/2000000000 : ℝ)*x 0 + (2619741433/5000000000 : ℝ)*x 1 + (2710516031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (425514243/2000000000 : ℝ)^2103 ≤ (25253431909/195312500000 : ℝ)^1591 := by
    have hnat : (425514243 : ℕ)^2103*195312500000^1591 ≤ 25253431909^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425514243 2000000000 25253431909 195312500000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2619741433/5000000000 : ℝ)^2103 ≤ (1329849832349/3125000000000 : ℝ)^1591 := by
    have hnat : (2619741433 : ℕ)^2103*3125000000000^1591 ≤ 1329849832349^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2619741433 5000000000 1329849832349 3125000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710516031/5000000000 : ℝ)^2103 ≤ (5564381026193/12500000000000 : ℝ)^1591 := by
    have hnat : (2710516031 : ℕ)^2103*12500000000000^1591 ≤ 5564381026193^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710516031 5000000000 5564381026193 12500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-425514243/2000000000 : ℝ), (2619741433/5000000000 : ℝ), (2710516031/5000000000 : ℝ)] ![(25253431909/195312500000 : ℝ), (1329849832349/3125000000000 : ℝ), (5564381026193/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-425514243/2000000000 : ℝ)|^2103 ≤ (25253431909/195312500000 : ℝ)^1591
        have hw : |(-425514243/2000000000 : ℝ)|=(425514243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2619741433/5000000000 : ℝ)|^2103 ≤ (1329849832349/3125000000000 : ℝ)^1591
        have hw : |(2619741433/5000000000 : ℝ)|=(2619741433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710516031/5000000000 : ℝ)|^2103 ≤ (5564381026193/12500000000000 : ℝ)^1591
        have hw : |(2710516031/5000000000 : ℝ)|=(2710516031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s3_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305412029/10000000000 : ℝ)*x 0 + (-2038678051/10000000000 : ℝ)*x 1 + (2710515967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305412029/10000000000 : ℝ)^2103 ≤ (43264424071147/100000000000000 : ℝ)^1591 := by
    have hnat : (5305412029 : ℕ)^2103*100000000000000^1591 ≤ 43264424071147^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305412029 10000000000 43264424071147 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2038678051/10000000000 : ℝ)^2103 ≤ (12220529098447/100000000000000 : ℝ)^1591 := by
    have hnat : (2038678051 : ℕ)^2103*100000000000000^1591 ≤ 12220529098447^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038678051 10000000000 12220529098447 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2710515967/5000000000 : ℝ)^2103 ≤ (22257523410109/50000000000000 : ℝ)^1591 := by
    have hnat : (2710515967 : ℕ)^2103*50000000000000^1591 ≤ 22257523410109^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710515967 5000000000 22257523410109 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305412029/10000000000 : ℝ), (-2038678051/10000000000 : ℝ), (2710515967/5000000000 : ℝ)] ![(43264424071147/100000000000000 : ℝ), (12220529098447/100000000000000 : ℝ), (22257523410109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305412029/10000000000 : ℝ)|^2103 ≤ (43264424071147/100000000000000 : ℝ)^1591
        have hw : |(5305412029/10000000000 : ℝ)|=(5305412029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2038678051/10000000000 : ℝ)|^2103 ≤ (12220529098447/100000000000000 : ℝ)^1591
        have hw : |(-2038678051/10000000000 : ℝ)|=(2038678051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2710515967/5000000000 : ℝ)|^2103 ≤ (22257523410109/50000000000000 : ℝ)^1591
        have hw : |(2710515967/5000000000 : ℝ)|=(2710515967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s3_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305411919/10000000000 : ℝ)*x 0 + (1084206413/2000000000 : ℝ)*x 1 + (-2038678021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305411919/10000000000 : ℝ)^2103 ≤ (43264422885451/100000000000000 : ℝ)^1591 := by
    have hnat : (5305411919 : ℕ)^2103*100000000000000^1591 ≤ 43264422885451^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305411919 10000000000 43264422885451 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084206413/2000000000 : ℝ)^2103 ≤ (22257524121053/50000000000000 : ℝ)^1591 := by
    have hnat : (1084206413 : ℕ)^2103*50000000000000^1591 ≤ 22257524121053^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084206413 2000000000 22257524121053 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2038678021/10000000000 : ℝ)^2103 ≤ (2444105772149/20000000000000 : ℝ)^1591 := by
    have hnat : (2038678021 : ℕ)^2103*20000000000000^1591 ≤ 2444105772149^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038678021 10000000000 2444105772149 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305411919/10000000000 : ℝ), (1084206413/2000000000 : ℝ), (-2038678021/10000000000 : ℝ)] ![(43264422885451/100000000000000 : ℝ), (22257524121053/50000000000000 : ℝ), (2444105772149/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305411919/10000000000 : ℝ)|^2103 ≤ (43264422885451/100000000000000 : ℝ)^1591
        have hw : |(5305411919/10000000000 : ℝ)|=(5305411919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084206413/2000000000 : ℝ)|^2103 ≤ (22257524121053/50000000000000 : ℝ)^1591
        have hw : |(1084206413/2000000000 : ℝ)|=(1084206413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2038678021/10000000000 : ℝ)|^2103 ≤ (2444105772149/20000000000000 : ℝ)^1591
        have hw : |(-2038678021/10000000000 : ℝ)|=(2038678021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s3_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2176076933/5000000000 : ℝ)*x 0 + (4539278583/10000000000 : ℝ)*x 1 + (104315713/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2176076933/5000000000 : ℝ)^2103 ≤ (33299337022223/100000000000000 : ℝ)^1591 := by
    have hnat : (2176076933 : ℕ)^2103*100000000000000^1591 ≤ 33299337022223^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2176076933 5000000000 33299337022223 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539278583/10000000000 : ℝ)^2103 ≤ (17602392987393/50000000000000 : ℝ)^1591 := by
    have hnat : (4539278583 : ℕ)^2103*50000000000000^1591 ≤ 17602392987393^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539278583 10000000000 17602392987393 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104315713/250000000 : ℝ)^2103 ≤ (6299175398407/20000000000000 : ℝ)^1591 := by
    have hnat : (104315713 : ℕ)^2103*20000000000000^1591 ≤ 6299175398407^1591*250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104315713 250000000 6299175398407 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2176076933/5000000000 : ℝ), (4539278583/10000000000 : ℝ), (104315713/250000000 : ℝ)] ![(33299337022223/100000000000000 : ℝ), (17602392987393/50000000000000 : ℝ), (6299175398407/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2176076933/5000000000 : ℝ)|^2103 ≤ (33299337022223/100000000000000 : ℝ)^1591
        have hw : |(2176076933/5000000000 : ℝ)|=(2176076933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539278583/10000000000 : ℝ)|^2103 ≤ (17602392987393/50000000000000 : ℝ)^1591
        have hw : |(4539278583/10000000000 : ℝ)|=(4539278583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104315713/250000000 : ℝ)|^2103 ≤ (6299175398407/20000000000000 : ℝ)^1591
        have hw : |(104315713/250000000 : ℝ)|=(104315713/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4071/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1881/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10851/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7361/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4071/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1881/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4071/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1881/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4071/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1881/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4071/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1881/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4071/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1881/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4071/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1881/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1881/20000 : ℝ) ^ (8411/2048 : ℝ) ≤ (6076489706154861/100000000000000000000 : ℝ) := by
    have hpowers : (1881/20000 : ℝ)^8411 ≤ (6076489706154861/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1881 : ℕ)^8411*100000000000000000000^2048 ≤ 6076489706154861^2048*20000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1881 20000 6076489706154861 100000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1881/20000 : ℝ)) (X := (6076489706154861/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4071/25000 : ℝ) ^ (8411/2048 : ℝ) ≤ (14477553034244691/25000000000000000000 : ℝ) := by
    have hpowers : (4071/25000 : ℝ)^8411 ≤ (14477553034244691/25000000000000000000 : ℝ)^2048 := by
      have hnat : (4071 : ℕ)^8411*25000000000000000000^2048 ≤ 14477553034244691^2048*25000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4071 25000 14477553034244691 25000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4071/25000 : ℝ)) (X := (14477553034244691/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006076489706154861/50000000000000000000 : ℝ) ≤ (10000295900104343/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (50006076489706154861/50000000000000000000 : ℝ)^2048 ≤ (10000295900104343/10000000000000000 : ℝ)^8411 := by
      have hnat : (50006076489706154861 : ℕ)^2048*10000000000000000^8411 ≤ 10000295900104343^8411*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006076489706154861 50000000000000000000 10000295900104343 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000295900104343/10000000000000000 : ℝ)) (X := (50006076489706154861/50000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (800511893614745069/800000000000000000 : ℝ) ≤ (1000155763952129/1000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (800511893614745069/800000000000000000 : ℝ)^2048 ≤ (1000155763952129/1000000000000000 : ℝ)^8411 := by
      have hnat : (800511893614745069 : ℕ)^2048*1000000000000000^8411 ≤ 1000155763952129^8411*800000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800511893614745069 800000000000000000 1000155763952129 1000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000155763952129/1000000000000000 : ℝ)) (X := (800511893614745069/800000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12514477553034244691/12500000000000000000 : ℝ) ≤ (10002819378938237/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (12514477553034244691/12500000000000000000 : ℝ)^2048 ≤ (10002819378938237/10000000000000000 : ℝ)^8411 := by
      have hnat : (12514477553034244691 : ℕ)^2048*10000000000000000^8411 ≤ 10002819378938237^8411*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12514477553034244691 12500000000000000000 10002819378938237 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002819378938237/10000000000000000 : ℝ)) (X := (12514477553034244691/12500000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6076489706154861/100000000000000000000 : ℝ) ≤ ((22922767392795000809/22930000000000000000 : ℝ)+2*(420579805649/229300000000000 : ℝ)*(1881/20000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (22922767392795000809/22930000000000000000 : ℝ)+2*(420579805649/229300000000000 : ℝ)*(1881/20000 : ℝ)=(10000295900104343/10000000000000000 : ℝ) by norm_num, show 1+2*(6076489706154861/100000000000000000000 : ℝ)=(50006076489706154861/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14477553034244691/25000000000000000000 : ℝ)+(6076489706154861/100000000000000000000 : ℝ) ≤ ((22922767392795000809/22930000000000000000 : ℝ)+(420579805649/229300000000000 : ℝ)*((4071/25000 : ℝ)+(1881/20000 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (22922767392795000809/22930000000000000000 : ℝ)+(420579805649/229300000000000 : ℝ)*((4071/25000 : ℝ)+(1881/20000 : ℝ))=(1000155763952129/1000000000000000 : ℝ) by norm_num, show 1+(14477553034244691/25000000000000000000 : ℝ)+(6076489706154861/100000000000000000000 : ℝ)=(800511893614745069/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14477553034244691/25000000000000000000 : ℝ) ≤ ((22922767392795000809/22930000000000000000 : ℝ)+2*(420579805649/229300000000000 : ℝ)*(4071/25000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (22922767392795000809/22930000000000000000 : ℝ)+2*(420579805649/229300000000000 : ℝ)*(4071/25000 : ℝ)=(10002819378938237/10000000000000000 : ℝ) by norm_num, show 1+2*(14477553034244691/25000000000000000000 : ℝ)=(12514477553034244691/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22922767392795000809/22930000000000000000 : ℝ)*(X 1 0+X 2 0)+(420579805649/229300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (1881/20000 : ℝ)) (hi := (4071/25000 : ℝ)) (c := (22922767392795000809/22930000000000000000 : ℝ)) (alpha := (420579805649/229300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22922767392795000809/22930000000000000000 : ℝ)*(X 0 1+X 2 1)+(420579805649/229300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (1881/20000 : ℝ)) (hi := (4071/25000 : ℝ)) (c := (22922767392795000809/22930000000000000000 : ℝ)) (alpha := (420579805649/229300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22922767392795000809/22930000000000000000 : ℝ)*(X 0 2+X 1 2)+(420579805649/229300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (1881/20000 : ℝ)) (hi := (4071/25000 : ℝ)) (c := (22922767392795000809/22930000000000000000 : ℝ)) (alpha := (420579805649/229300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1063778099/5000000000 : ℝ)*X 0 0+(271085511/500000000 : ℝ)*X 0 1+(2619404221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676000963/5000000000 : ℝ)*X 1 0+(-2220901557/10000000000 : ℝ)*X 1 1+(1309702161/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676000897/5000000000 : ℝ)*X 2 0+(523880901/1000000000 : ℝ)*X 2 1+(-1776721/8000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4352123763/10000000000 : ℝ)*X 0 0+(2085629741/5000000000 : ℝ)*X 0 1+(2270320287/5000000000 : ℝ)*X 0 2+(4352123763/10000000000 : ℝ)*X 1 0+(2085629741/5000000000 : ℝ)*X 1 1+(2270320287/5000000000 : ℝ)*X 1 2+(4352123763/10000000000 : ℝ)*X 2 0+(2085629741/5000000000 : ℝ)*X 2 1+(2270320287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-425514243/2000000000 : ℝ)*X 0 0+(2619741433/5000000000 : ℝ)*X 0 1+(2710516031/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305412029/10000000000 : ℝ)*X 1 0+(-2038678051/10000000000 : ℝ)*X 1 1+(2710515967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305411919/10000000000 : ℝ)*X 2 0+(1084206413/2000000000 : ℝ)*X 2 1+(-2038678021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2176076933/5000000000 : ℝ)*X 0 0+(4539278583/10000000000 : ℝ)*X 0 1+(104315713/250000000 : ℝ)*X 0 2+(2176076933/5000000000 : ℝ)*X 1 0+(4539278583/10000000000 : ℝ)*X 1 1+(104315713/250000000 : ℝ)*X 1 2+(2176076933/5000000000 : ℝ)*X 2 0+(4539278583/10000000000 : ℝ)*X 2 1+(104315713/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2725423938369936219866559003/286625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (57483697/4000000000000 : ℝ)*(base19) + (1042562771/100000000000000 : ℝ)*(base23) + (138981489/100000000000000 : ℝ)*(lower2) + (10627323/20000000000000 : ℝ)*(upper3) + (11202519/6250000000000 : ℝ)*(upper5) + (1021843942365911/25000000000000 : ℝ)*(major0) + (1021843942365911/25000000000000 : ℝ)*(major1) + (1021843942365911/25000000000000 : ℝ)*(major2) + (21357224926569/390625000000 : ℝ)*(sp0) + (2733744418865059/50000000000000 : ℝ)*(sp1) + (5467489232259771/100000000000000 : ℝ)*(sp2) + (67681165465027/2500000000000 : ℝ)*(sp3) + (20346810439/50000000000000 : ℝ)*(sp4) + (14328547827/100000000000000 : ℝ)*(sp7) + (2707260947148907/100000000000000 : ℝ)*(f.failure) + (5467490274822543/100000000000000 : ℝ)*(f.sum) + (2569557673843/1433125000000000000000000000 : ℝ)*base66 + (5164411665793671999/573250000000000000000000000000000 : ℝ)*base67 + (7222280707239921999/573250000000000000000000000000000 : ℝ)*base69 + (861191097850421999/573250000000000000000000000000000 : ℝ)*base71 + (30453771628419/11465000000000000000000000000 : ℝ)*base74 + (1456324203241078001/573250000000000000000000000000000 : ℝ)*base76 + (4265251690235921999/573250000000000000000000000000000 : ℝ)*base77 + (2634456401362828001/573250000000000000000000000000000 : ℝ)*base80 + (15452902518653/5732500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (41600203/10000000000000000000000 : ℝ)*base90 + (41600203/10000000000000000000000 : ℝ)*base92 + (41600203/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (404109864067524347652638049/143312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (401561617/50000000000000 : ℝ)*(base19) + (368624127/50000000000000 : ℝ)*(base23) + (219823/2000000000000 : ℝ)*(upper3) + (15389773/50000000000000 : ℝ)*(lower4) + (109413111/100000000000000 : ℝ)*(upper5) + (514721571945071/12500000000000 : ℝ)*(major0) + (514721571945071/12500000000000 : ℝ)*(major1) + (514721571945071/12500000000000 : ℝ)*(major2) + (7854431863/50000000000000 : ℝ)*(sp1) + (14605780617/100000000000000 : ℝ)*(sp2) + (2754075438815263/50000000000000 : ℝ)*(sp4) + (2754067182821783/50000000000000 : ℝ)*(sp5) + (1101627106920331/20000000000000 : ℝ)*(sp6) + (2727394179497901/100000000000000 : ℝ)*(sp7) + (2727394179497901/100000000000000 : ℝ)*(f.failure) + (2754075438815263/50000000000000 : ℝ)*(f.sum) + (1513697055099/1433125000000000000000000000 : ℝ)*base65 + (4276582780118087439/286625000000000000000000000000000 : ℝ)*base67 + (1584904793796962439/286625000000000000000000000000000 : ℝ)*base69 + (4481776139492962439/286625000000000000000000000000000 : ℝ)*base71 + (12905183147643/11465000000000000000000000000 : ℝ)*base74 + (1900605155325962439/286625000000000000000000000000000 : ℝ)*base75 + (2732744199014337439/286625000000000000000000000000000 : ℝ)*base77 + (1546634653605962439/286625000000000000000000000000000 : ℝ)*base79 + (21513005044157/11465000000000000000000000000 : ℝ)*base81 + (58890829/10000000000000000000000 : ℝ)*base90 + (58890829/10000000000000000000000 : ℝ)*base92 + (58890829/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1219_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4071/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1881/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1219_s4_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2129998319/10000000000 : ℝ)*x 0 + (5398437837/10000000000 : ℝ)*x 1 + (2630240437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2129998319/10000000000 : ℝ)^2103 ≤ (809328595839/6250000000000 : ℝ)^1591 := by
    have hnat : (2129998319 : ℕ)^2103*6250000000000^1591 ≤ 809328595839^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2129998319 10000000000 809328595839 6250000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398437837/10000000000 : ℝ)^2103 ≤ (44269972770537/100000000000000 : ℝ)^1591 := by
    have hnat : (5398437837 : ℕ)^2103*100000000000000^1591 ≤ 44269972770537^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398437837 10000000000 44269972770537 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630240437/5000000000 : ℝ)^2103 ≤ (42780769683187/100000000000000 : ℝ)^1591 := by
    have hnat : (2630240437 : ℕ)^2103*100000000000000^1591 ≤ 42780769683187^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630240437 5000000000 42780769683187 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2129998319/10000000000 : ℝ), (5398437837/10000000000 : ℝ), (2630240437/5000000000 : ℝ)] ![(809328595839/6250000000000 : ℝ), (44269972770537/100000000000000 : ℝ), (42780769683187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2129998319/10000000000 : ℝ)|^2103 ≤ (809328595839/6250000000000 : ℝ)^1591
        have hw : |(-2129998319/10000000000 : ℝ)|=(2129998319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398437837/10000000000 : ℝ)|^2103 ≤ (44269972770537/100000000000000 : ℝ)^1591
        have hw : |(5398437837/10000000000 : ℝ)|=(5398437837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630240437/5000000000 : ℝ)|^2103 ≤ (42780769683187/100000000000000 : ℝ)^1591
        have hw : |(2630240437/5000000000 : ℝ)|=(2630240437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s4_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (668268433/1250000000 : ℝ)*x 0 + (-1100027089/5000000000 : ℝ)*x 1 + (2630240339/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668268433/1250000000 : ℝ)^2103 ≤ (43704055314191/100000000000000 : ℝ)^1591 := by
    have hnat : (668268433 : ℕ)^2103*100000000000000^1591 ≤ 43704055314191^1591*1250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668268433 1250000000 43704055314191 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100027089/5000000000 : ℝ)^2103 ≤ (13515177087957/100000000000000 : ℝ)^1591 := by
    have hnat : (1100027089 : ℕ)^2103*100000000000000^1591 ≤ 13515177087957^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100027089 5000000000 13515177087957 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630240339/5000000000 : ℝ)^2103 ≤ (21390383788133/50000000000000 : ℝ)^1591 := by
    have hnat : (2630240339 : ℕ)^2103*50000000000000^1591 ≤ 21390383788133^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630240339 5000000000 21390383788133 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668268433/1250000000 : ℝ), (-1100027089/5000000000 : ℝ), (2630240339/5000000000 : ℝ)] ![(43704055314191/100000000000000 : ℝ), (13515177087957/100000000000000 : ℝ), (21390383788133/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668268433/1250000000 : ℝ)|^2103 ≤ (43704055314191/100000000000000 : ℝ)^1591
        have hw : |(668268433/1250000000 : ℝ)|=(668268433/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100027089/5000000000 : ℝ)|^2103 ≤ (13515177087957/100000000000000 : ℝ)^1591
        have hw : |(-1100027089/5000000000 : ℝ)|=(1100027089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630240339/5000000000 : ℝ)|^2103 ≤ (21390383788133/50000000000000 : ℝ)^1591
        have hw : |(2630240339/5000000000 : ℝ)|=(2630240339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s4_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336536617/2500000000 : ℝ)*x 0 + (5260481041/10000000000 : ℝ)*x 1 + (-137503439/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336536617/2500000000 : ℝ)^2103 ≤ (43704044551789/100000000000000 : ℝ)^1591 := by
    have hnat : (1336536617 : ℕ)^2103*100000000000000^1591 ≤ 43704044551789^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336536617 2500000000 43704044551789 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260481041/10000000000 : ℝ)^2103 ≤ (4278077147837/10000000000000 : ℝ)^1591 := by
    have hnat : (5260481041 : ℕ)^2103*10000000000000^1591 ≤ 4278077147837^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260481041 10000000000 4278077147837 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (137503439/625000000 : ℝ)^2103 ≤ (13515183957501/100000000000000 : ℝ)^1591 := by
    have hnat : (137503439 : ℕ)^2103*100000000000000^1591 ≤ 13515183957501^1591*625000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137503439 625000000 13515183957501 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336536617/2500000000 : ℝ), (5260481041/10000000000 : ℝ), (-137503439/625000000 : ℝ)] ![(43704044551789/100000000000000 : ℝ), (4278077147837/10000000000000 : ℝ), (13515183957501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336536617/2500000000 : ℝ)|^2103 ≤ (43704044551789/100000000000000 : ℝ)^1591
        have hw : |(1336536617/2500000000 : ℝ)|=(1336536617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260481041/10000000000 : ℝ)|^2103 ≤ (4278077147837/10000000000000 : ℝ)^1591
        have hw : |(5260481041/10000000000 : ℝ)|=(5260481041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-137503439/625000000 : ℝ)|^2103 ≤ (13515183957501/100000000000000 : ℝ)^1591
        have hw : |(-137503439/625000000 : ℝ)|=(137503439/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s4_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4353584141/10000000000 : ℝ)*x 0 + (2108228539/5000000000 : ℝ)*x 1 + (899013903/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353584141/10000000000 : ℝ)^2103 ≤ (16656901419323/50000000000000 : ℝ)^1591 := by
    have hnat : (4353584141 : ℕ)^2103*50000000000000^1591 ≤ 16656901419323^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353584141 10000000000 16656901419323 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108228539/5000000000 : ℝ)^2103 ≤ (31933905035749/100000000000000 : ℝ)^1591 := by
    have hnat : (2108228539 : ℕ)^2103*100000000000000^1591 ≤ 31933905035749^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108228539 5000000000 31933905035749 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899013903/2000000000 : ℝ)^2103 ≤ (6950458420153/20000000000000 : ℝ)^1591 := by
    have hnat : (899013903 : ℕ)^2103*20000000000000^1591 ≤ 6950458420153^1591*2000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899013903 2000000000 6950458420153 20000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353584141/10000000000 : ℝ), (2108228539/5000000000 : ℝ), (899013903/2000000000 : ℝ)] ![(16656901419323/50000000000000 : ℝ), (31933905035749/100000000000000 : ℝ), (6950458420153/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353584141/10000000000 : ℝ)|^2103 ≤ (16656901419323/50000000000000 : ℝ)^1591
        have hw : |(4353584141/10000000000 : ℝ)|=(4353584141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2108228539/5000000000 : ℝ)|^2103 ≤ (31933905035749/100000000000000 : ℝ)^1591
        have hw : |(2108228539/5000000000 : ℝ)|=(2108228539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(899013903/2000000000 : ℝ)|^2103 ≤ (6950458420153/20000000000000 : ℝ)^1591
        have hw : |(899013903/2000000000 : ℝ)|=(899013903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s4_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130004881/10000000000 : ℝ)*x 0 + (1315216379/2500000000 : ℝ)*x 1 + (674756439/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130004881/10000000000 : ℝ)^2103 ≤ (1618663783131/12500000000000 : ℝ)^1591 := by
    have hnat : (2130004881 : ℕ)^2103*12500000000000^1591 ≤ 1618663783131^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130004881 10000000000 1618663783131 12500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315216379/2500000000 : ℝ)^2103 ≤ (21392452239437/50000000000000 : ℝ)^1591 := by
    have hnat : (1315216379 : ℕ)^2103*50000000000000^1591 ≤ 21392452239437^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315216379 2500000000 21392452239437 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674756439/1250000000 : ℝ)^2103 ≤ (44265785239341/100000000000000 : ℝ)^1591 := by
    have hnat : (674756439 : ℕ)^2103*100000000000000^1591 ≤ 44265785239341^1591*1250000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674756439 1250000000 44265785239341 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130004881/10000000000 : ℝ), (1315216379/2500000000 : ℝ), (674756439/1250000000 : ℝ)] ![(1618663783131/12500000000000 : ℝ), (21392452239437/50000000000000 : ℝ), (44265785239341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130004881/10000000000 : ℝ)|^2103 ≤ (1618663783131/12500000000000 : ℝ)^1591
        have hw : |(-2130004881/10000000000 : ℝ)|=(2130004881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315216379/2500000000 : ℝ)|^2103 ≤ (21392452239437/50000000000000 : ℝ)^1591
        have hw : |(1315216379/2500000000 : ℝ)|=(1315216379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674756439/1250000000 : ℝ)|^2103 ≤ (44265785239341/100000000000000 : ℝ)^1591
        have hw : |(674756439/1250000000 : ℝ)|=(674756439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s4_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (331937711/625000000 : ℝ)*x 0 + (-2062484063/10000000000 : ℝ)*x 1 + (5398051913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331937711/625000000 : ℝ)^2103 ≤ (43324703755599/100000000000000 : ℝ)^1591 := by
    have hnat : (331937711 : ℕ)^2103*100000000000000^1591 ≤ 43324703755599^1591*625000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331937711 625000000 43324703755599 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062484063/10000000000 : ℝ)^2103 ≤ (3102376660767/25000000000000 : ℝ)^1591 := by
    have hnat : (2062484063 : ℕ)^2103*25000000000000^1591 ≤ 3102376660767^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062484063 10000000000 3102376660767 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5398051913/10000000000 : ℝ)^2103 ≤ (4426578958589/10000000000000 : ℝ)^1591 := by
    have hnat : (5398051913 : ℕ)^2103*10000000000000^1591 ≤ 4426578958589^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398051913 10000000000 4426578958589 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331937711/625000000 : ℝ), (-2062484063/10000000000 : ℝ), (5398051913/10000000000 : ℝ)] ![(43324703755599/100000000000000 : ℝ), (3102376660767/25000000000000 : ℝ), (4426578958589/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331937711/625000000 : ℝ)|^2103 ≤ (43324703755599/100000000000000 : ℝ)^1591
        have hw : |(331937711/625000000 : ℝ)|=(331937711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2062484063/10000000000 : ℝ)|^2103 ≤ (3102376660767/25000000000000 : ℝ)^1591
        have hw : |(-2062484063/10000000000 : ℝ)|=(2062484063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5398051913/10000000000 : ℝ)|^2103 ≤ (4426578958589/10000000000000 : ℝ)^1591
        have hw : |(5398051913/10000000000 : ℝ)|=(5398051913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s4_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (33193769/62500000 : ℝ)*x 0 + (5398052383/10000000000 : ℝ)*x 1 + (-2062483877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33193769/62500000 : ℝ)^2103 ≤ (43324700132607/100000000000000 : ℝ)^1591 := by
    have hnat : (33193769 : ℕ)^2103*100000000000000^1591 ≤ 43324700132607^1591*62500000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33193769 62500000 43324700132607 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5398052383/10000000000 : ℝ)^2103 ≤ (885315893607/2000000000000 : ℝ)^1591 := by
    have hnat : (5398052383 : ℕ)^2103*2000000000000^1591 ≤ 885315893607^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398052383 10000000000 885315893607 2000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2062483877/10000000000 : ℝ)^2103 ≤ (12409505163803/100000000000000 : ℝ)^1591 := by
    have hnat : (2062483877 : ℕ)^2103*100000000000000^1591 ≤ 12409505163803^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062483877 10000000000 12409505163803 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(33193769/62500000 : ℝ), (5398052383/10000000000 : ℝ), (-2062483877/10000000000 : ℝ)] ![(43324700132607/100000000000000 : ℝ), (885315893607/2000000000000 : ℝ), (12409505163803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(33193769/62500000 : ℝ)|^2103 ≤ (43324700132607/100000000000000 : ℝ)^1591
        have hw : |(33193769/62500000 : ℝ)|=(33193769/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5398052383/10000000000 : ℝ)|^2103 ≤ (885315893607/2000000000000 : ℝ)^1591
        have hw : |(5398052383/10000000000 : ℝ)|=(5398052383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2062483877/10000000000 : ℝ)|^2103 ≤ (12409505163803/100000000000000 : ℝ)^1591
        have hw : |(-2062483877/10000000000 : ℝ)|=(2062483877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s4_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (68024963/156250000 : ℝ)*x 0 + (4494293397/10000000000 : ℝ)*x 1 + (1054308917/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (68024963/156250000 : ℝ)^2103 ≤ (8328484823511/25000000000000 : ℝ)^1591 := by
    have hnat : (68024963 : ℕ)^2103*25000000000000^1591 ≤ 8328484823511^1591*156250000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68024963 156250000 8328484823511 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4494293397/10000000000 : ℝ)^2103 ≤ (3474436103001/10000000000000 : ℝ)^1591 := by
    have hnat : (4494293397 : ℕ)^2103*10000000000000^1591 ≤ 3474436103001^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494293397 10000000000 3474436103001 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054308917/2500000000 : ℝ)^2103 ≤ (31941699659621/100000000000000 : ℝ)^1591 := by
    have hnat : (1054308917 : ℕ)^2103*100000000000000^1591 ≤ 31941699659621^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054308917 2500000000 31941699659621 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(68024963/156250000 : ℝ), (4494293397/10000000000 : ℝ), (1054308917/2500000000 : ℝ)] ![(8328484823511/25000000000000 : ℝ), (3474436103001/10000000000000 : ℝ), (31941699659621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(68024963/156250000 : ℝ)|^2103 ≤ (8328484823511/25000000000000 : ℝ)^1591
        have hw : |(68024963/156250000 : ℝ)|=(68024963/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4494293397/10000000000 : ℝ)|^2103 ≤ (3474436103001/10000000000000 : ℝ)^1591
        have hw : |(4494293397/10000000000 : ℝ)|=(4494293397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054308917/2500000000 : ℝ)|^2103 ≤ (31941699659621/100000000000000 : ℝ)^1591
        have hw : |(1054308917/2500000000 : ℝ)|=(1054308917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s4_8 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-38904353/10000000000 : ℝ)*x 0 + (1479050643/2500000000 : ℝ)*x 1 + (2958126699/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38904353/10000000000 : ℝ)^2103 ≤ (32614076237/50000000000000 : ℝ)^1591 := by
    have hnat : (38904353 : ℕ)^2103*50000000000000^1591 ≤ 32614076237^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38904353 10000000000 32614076237 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1479050643/2500000000 : ℝ)^2103 ≤ (4996710221359/10000000000000 : ℝ)^1591 := by
    have hnat : (1479050643 : ℕ)^2103*10000000000000^1591 ≤ 4996710221359^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1479050643 2500000000 4996710221359 10000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2958126699/5000000000 : ℝ)^2103 ≤ (49967669623287/100000000000000 : ℝ)^1591 := by
    have hnat : (2958126699 : ℕ)^2103*100000000000000^1591 ≤ 49967669623287^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958126699 5000000000 49967669623287 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38904353/10000000000 : ℝ), (1479050643/2500000000 : ℝ), (2958126699/5000000000 : ℝ)] ![(32614076237/50000000000000 : ℝ), (4996710221359/10000000000000 : ℝ), (49967669623287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38904353/10000000000 : ℝ)|^2103 ≤ (32614076237/50000000000000 : ℝ)^1591
        have hw : |(-38904353/10000000000 : ℝ)|=(38904353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1479050643/2500000000 : ℝ)|^2103 ≤ (4996710221359/10000000000000 : ℝ)^1591
        have hw : |(1479050643/2500000000 : ℝ)|=(1479050643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2958126699/5000000000 : ℝ)|^2103 ≤ (49967669623287/100000000000000 : ℝ)^1591
        have hw : |(2958126699/5000000000 : ℝ)|=(2958126699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5657/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10851/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7361/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10851/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10851/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7361/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10851/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10851/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7361/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10851/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10851/100000 : ℝ) ^ (8411/2048 : ℝ) ≤ (2186595072661103/20000000000000000000 : ℝ) := by
    have hpowers : (10851/100000 : ℝ)^8411 ≤ (2186595072661103/20000000000000000000 : ℝ)^2048 := by
      have hnat : (10851 : ℕ)^8411*20000000000000000000^2048 ≤ 2186595072661103^2048*100000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10851 100000 2186595072661103 20000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10851/100000 : ℝ)) (X := (2186595072661103/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7361/50000 : ℝ) ^ (8411/2048 : ℝ) ≤ (7654643172018003/20000000000000000000 : ℝ) := by
    have hpowers : (7361/50000 : ℝ)^8411 ≤ (7654643172018003/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7361 : ℕ)^8411*20000000000000000000^2048 ≤ 7654643172018003^2048*50000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7361 50000 7654643172018003 20000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7361/50000 : ℝ)) (X := (7654643172018003/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002186595072661103/10000000000000000000 : ℝ) ≤ (10000532371462761/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (10002186595072661103/10000000000000000000 : ℝ)^2048 ≤ (10000532371462761/10000000000000000 : ℝ)^8411 := by
      have hnat : (10002186595072661103 : ℕ)^2048*10000000000000000^8411 ≤ 10000532371462761^8411*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002186595072661103 10000000000000000000 10000532371462761 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000532371462761/10000000000000000 : ℝ)) (X := (10002186595072661103/10000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004920619122339553/10000000000000000000 : ℝ) ≤ (2000239580379131/2000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (10004920619122339553/10000000000000000000 : ℝ)^2048 ≤ (2000239580379131/2000000000000000 : ℝ)^8411 := by
      have hnat : (10004920619122339553 : ℕ)^2048*2000000000000000^8411 ≤ 2000239580379131^8411*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004920619122339553 10000000000000000000 2000239580379131 2000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000239580379131/2000000000000000 : ℝ)) (X := (10004920619122339553/10000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007654643172018003/10000000000000000000 : ℝ) ≤ (10001863432328549/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (10007654643172018003/10000000000000000000 : ℝ)^2048 ≤ (10001863432328549/10000000000000000 : ℝ)^8411 := by
      have hnat : (10007654643172018003 : ℕ)^2048*10000000000000000^8411 ≤ 10001863432328549^8411*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007654643172018003 10000000000000000000 10001863432328549 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001863432328549/10000000000000000 : ℝ)) (X := (10007654643172018003/10000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2186595072661103/20000000000000000000 : ℝ) ≤ ((38697617468477682243/38710000000000000000 : ℝ)+2*(332765216447/193550000000000 : ℝ)*(10851/100000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (38697617468477682243/38710000000000000000 : ℝ)+2*(332765216447/193550000000000 : ℝ)*(10851/100000 : ℝ)=(10000532371462761/10000000000000000 : ℝ) by norm_num, show 1+2*(2186595072661103/20000000000000000000 : ℝ)=(10002186595072661103/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7654643172018003/20000000000000000000 : ℝ)+(2186595072661103/20000000000000000000 : ℝ) ≤ ((38697617468477682243/38710000000000000000 : ℝ)+(332765216447/193550000000000 : ℝ)*((7361/50000 : ℝ)+(10851/100000 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (38697617468477682243/38710000000000000000 : ℝ)+(332765216447/193550000000000 : ℝ)*((7361/50000 : ℝ)+(10851/100000 : ℝ))=(2000239580379131/2000000000000000 : ℝ) by norm_num, show 1+(7654643172018003/20000000000000000000 : ℝ)+(2186595072661103/20000000000000000000 : ℝ)=(10004920619122339553/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7654643172018003/20000000000000000000 : ℝ) ≤ ((38697617468477682243/38710000000000000000 : ℝ)+2*(332765216447/193550000000000 : ℝ)*(7361/50000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (38697617468477682243/38710000000000000000 : ℝ)+2*(332765216447/193550000000000 : ℝ)*(7361/50000 : ℝ)=(10001863432328549/10000000000000000 : ℝ) by norm_num, show 1+2*(7654643172018003/20000000000000000000 : ℝ)=(10007654643172018003/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38697617468477682243/38710000000000000000 : ℝ)*(X 1 0+X 2 0)+(332765216447/193550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (38697617468477682243/38710000000000000000 : ℝ)) (alpha := (332765216447/193550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38697617468477682243/38710000000000000000 : ℝ)*(X 0 1+X 2 1)+(332765216447/193550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (38697617468477682243/38710000000000000000 : ℝ)) (alpha := (332765216447/193550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38697617468477682243/38710000000000000000 : ℝ)*(X 0 2+X 1 2)+(332765216447/193550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (10851/100000 : ℝ)) (hi := (7361/50000 : ℝ)) (c := (38697617468477682243/38710000000000000000 : ℝ)) (alpha := (332765216447/193550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2129998319/10000000000 : ℝ)*X 0 0+(5398437837/10000000000 : ℝ)*X 0 1+(2630240437/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668268433/1250000000 : ℝ)*X 1 0+(-1100027089/5000000000 : ℝ)*X 1 1+(2630240339/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336536617/2500000000 : ℝ)*X 2 0+(5260481041/10000000000 : ℝ)*X 2 1+(-137503439/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353584141/10000000000 : ℝ)*X 0 0+(2108228539/5000000000 : ℝ)*X 0 1+(899013903/2000000000 : ℝ)*X 0 2+(4353584141/10000000000 : ℝ)*X 1 0+(2108228539/5000000000 : ℝ)*X 1 1+(899013903/2000000000 : ℝ)*X 1 2+(4353584141/10000000000 : ℝ)*X 2 0+(2108228539/5000000000 : ℝ)*X 2 1+(899013903/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2130004881/10000000000 : ℝ)*X 0 0+(1315216379/2500000000 : ℝ)*X 0 1+(674756439/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331937711/625000000 : ℝ)*X 1 0+(-2062484063/10000000000 : ℝ)*X 1 1+(5398051913/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((33193769/62500000 : ℝ)*X 2 0+(5398052383/10000000000 : ℝ)*X 2 1+(-2062483877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((68024963/156250000 : ℝ)*X 0 0+(4494293397/10000000000 : ℝ)*X 0 1+(1054308917/2500000000 : ℝ)*X 0 2+(68024963/156250000 : ℝ)*X 1 0+(4494293397/10000000000 : ℝ)*X 1 1+(1054308917/2500000000 : ℝ)*X 1 2+(68024963/156250000 : ℝ)*X 2 0+(4494293397/10000000000 : ℝ)*X 2 1+(1054308917/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-38904353/10000000000 : ℝ)*X 0 0+(1479050643/2500000000 : ℝ)*X 0 1+(2958126699/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s4_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3426825772198163231911047651/1935500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223232107/100000000000000 : ℝ)*(upper2) + (17326677/6250000000000 : ℝ)*(lower3) + (545296467/100000000000000 : ℝ)*(lower4) + (72857871/20000000000000 : ℝ)*(lower5) + (5418953721366219/100000000000000 : ℝ)*(major0) + (5418953721366219/100000000000000 : ℝ)*(major1) + (5418953721366219/100000000000000 : ℝ)*(major2) + (7248675985562751/100000000000000 : ℝ)*(sp0) + (1449734274955109/20000000000000 : ℝ)*(sp1) + (1812164531507747/25000000000000 : ℝ)*(sp2) + (1794613782988089/50000000000000 : ℝ)*(sp3) + (1055370453/12500000000000 : ℝ)*(sp5) + (21691708181/100000000000000 : ℝ)*(sp6) + (1916088209/50000000000000 : ℝ)*(sp8) + (1794613782988089/50000000000000 : ℝ)*(f.failure) + (7248679817739169/100000000000000 : ℝ)*(f.sum) + (1659272999158339/19355000000000000000000000000 : ℝ)*base66 + (39544552613562050783/3871000000000000000000000000000000 : ℝ)*base68 + (20705000399926949217/3871000000000000000000000000000000 : ℝ)*base69 + (377304442230047050783/3871000000000000000000000000000000 : ℝ)*base72 + (23437709150069/4838750000000000000000000000 : ℝ)*base73 + (4424523142637050783/3871000000000000000000000000000000 : ℝ)*base76 + (42302133612567050783/3871000000000000000000000000000000 : ℝ)*base78 + (8941320536529949217/3871000000000000000000000000000000 : ℝ)*base79 + (24379697370331/19355000000000000000000000000 : ℝ)*base81 + (59185881/5000000000000000000000 : ℝ)*base90 + (59185881/5000000000000000000000 : ℝ)*base92 + (59185881/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8356210298366179622209415277/1935500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10763751/20000000000000 : ℝ)*(upper2) + (83932839/100000000000000 : ℝ)*(upper3) + (61805031/50000000000000 : ℝ)*(lower4) + (5449368438478213/100000000000000 : ℝ)*(major0) + (5449368438478213/100000000000000 : ℝ)*(major1) + (5449368438478213/100000000000000 : ℝ)*(major2) + (7082896641/100000000000000 : ℝ)*(sp1) + (13144138181/50000000000000 : ℝ)*(sp2) + (566850399/6250000000000 : ℝ)*(sp3) + (3644680965367327/50000000000000 : ℝ)*(sp4) + (3644678494258383/50000000000000 : ℝ)*(sp5) + (3644668891568523/50000000000000 : ℝ)*(sp6) + (360936359202531/10000000000000 : ℝ)*(sp7) + (1070339377/50000000000000 : ℝ)*(sp8) + (1804686330815847/50000000000000 : ℝ)*(f.failure) + (227792627231669/3125000000000 : ℝ)*(f.sum) + (13421229001491/9677500000000000000000000000 : ℝ)*base65 + (4888756788019328241/3871000000000000000000000000000000 : ℝ)*base68 + (28114497454245328241/3871000000000000000000000000000000 : ℝ)*base70 + (17174078435150671759/3871000000000000000000000000000000 : ℝ)*base71 + (1109840903937/1209687500000000000000000000 : ℝ)*base73 + (5500983900818671759/3871000000000000000000000000000000 : ℝ)*base75 + (184280266721585328241/3871000000000000000000000000000000 : ℝ)*base78 + (1908035334687328241/3871000000000000000000000000000000 : ℝ)*base80 + (829802823641/2419375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (50539463/5000000000000000000000 : ℝ)*base90 + (50539463/5000000000000000000000 : ℝ)*base92 + (50539463/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1219_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7361/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10851/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1219_s5_0 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2130483183/10000000000 : ℝ)*x 0 + (1348240509/2500000000 : ℝ)*x 1 + (1316409573/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2130483183/10000000000 : ℝ)^2103 ≤ (6476576998167/50000000000000 : ℝ)^1591 := by
    have hnat : (2130483183 : ℕ)^2103*50000000000000^1591 ≤ 6476576998167^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130483183 10000000000 6476576998167 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348240509/2500000000 : ℝ)^2103 ≤ (22105313689729/50000000000000 : ℝ)^1591 := by
    have hnat : (1348240509 : ℕ)^2103*50000000000000^1591 ≤ 22105313689729^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348240509 2500000000 22105313689729 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316409573/2500000000 : ℝ)^2103 ≤ (42836218599547/100000000000000 : ℝ)^1591 := by
    have hnat : (1316409573 : ℕ)^2103*100000000000000^1591 ≤ 42836218599547^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316409573 2500000000 42836218599547 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2130483183/10000000000 : ℝ), (1348240509/2500000000 : ℝ), (1316409573/2500000000 : ℝ)] ![(6476576998167/50000000000000 : ℝ), (22105313689729/50000000000000 : ℝ), (42836218599547/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2130483183/10000000000 : ℝ)|^2103 ≤ (6476576998167/50000000000000 : ℝ)^1591
        have hw : |(-2130483183/10000000000 : ℝ)|=(2130483183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348240509/2500000000 : ℝ)|^2103 ≤ (22105313689729/50000000000000 : ℝ)^1591
        have hw : |(1348240509/2500000000 : ℝ)|=(1348240509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316409573/2500000000 : ℝ)|^2103 ≤ (42836218599547/100000000000000 : ℝ)^1591
        have hw : |(1316409573/2500000000 : ℝ)|=(1316409573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s5_1 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344764499/10000000000 : ℝ)*x 0 + (-2195063709/10000000000 : ℝ)*x 1 + (2632819151/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344764499/10000000000 : ℝ)^2103 ≤ (21844556067451/50000000000000 : ℝ)^1591 := by
    have hnat : (5344764499 : ℕ)^2103*50000000000000^1591 ≤ 21844556067451^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344764499 10000000000 21844556067451 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195063709/10000000000 : ℝ)^2103 ≤ (13474669144257/100000000000000 : ℝ)^1591 := by
    have hnat : (2195063709 : ℕ)^2103*100000000000000^1591 ≤ 13474669144257^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195063709 10000000000 13474669144257 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632819151/5000000000 : ℝ)^2103 ≤ (42836218707077/100000000000000 : ℝ)^1591 := by
    have hnat : (2632819151 : ℕ)^2103*100000000000000^1591 ≤ 42836218707077^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632819151 5000000000 42836218707077 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344764499/10000000000 : ℝ), (-2195063709/10000000000 : ℝ), (2632819151/5000000000 : ℝ)] ![(21844556067451/50000000000000 : ℝ), (13474669144257/100000000000000 : ℝ), (42836218707077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344764499/10000000000 : ℝ)|^2103 ≤ (21844556067451/50000000000000 : ℝ)^1591
        have hw : |(5344764499/10000000000 : ℝ)|=(5344764499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195063709/10000000000 : ℝ)|^2103 ≤ (13474669144257/100000000000000 : ℝ)^1591
        have hw : |(-2195063709/10000000000 : ℝ)|=(2195063709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632819151/5000000000 : ℝ)|^2103 ≤ (42836218707077/100000000000000 : ℝ)^1591
        have hw : |(2632819151/5000000000 : ℝ)|=(2632819151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s5_2 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336191127/2500000000 : ℝ)*x 0 + (2632819177/5000000000 : ℝ)*x 1 + (-548765907/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336191127/2500000000 : ℝ)^2103 ≤ (2730569514509/6250000000000 : ℝ)^1591 := by
    have hnat : (1336191127 : ℕ)^2103*6250000000000^1591 ≤ 2730569514509^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336191127 2500000000 2730569514509 6250000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632819177/5000000000 : ℝ)^2103 ≤ (42836219266233/100000000000000 : ℝ)^1591 := by
    have hnat : (2632819177 : ℕ)^2103*100000000000000^1591 ≤ 42836219266233^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632819177 5000000000 42836219266233 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548765907/2500000000 : ℝ)^2103 ≤ (1684333560877/12500000000000 : ℝ)^1591 := by
    have hnat : (548765907 : ℕ)^2103*12500000000000^1591 ≤ 1684333560877^1591*2500000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548765907 2500000000 1684333560877 12500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336191127/2500000000 : ℝ), (2632819177/5000000000 : ℝ), (-548765907/2500000000 : ℝ)] ![(2730569514509/6250000000000 : ℝ), (42836219266233/100000000000000 : ℝ), (1684333560877/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336191127/2500000000 : ℝ)|^2103 ≤ (2730569514509/6250000000000 : ℝ)^1591
        have hw : |(1336191127/2500000000 : ℝ)|=(1336191127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632819177/5000000000 : ℝ)|^2103 ≤ (42836219266233/100000000000000 : ℝ)^1591
        have hw : |(2632819177/5000000000 : ℝ)|=(2632819177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548765907/2500000000 : ℝ)|^2103 ≤ (1684333560877/12500000000000 : ℝ)^1591
        have hw : |(-548765907/2500000000 : ℝ)|=(548765907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s5_3 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4353870789/10000000000 : ℝ)*x 0 + (4227157117/10000000000 : ℝ)*x 1 + (22421477/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353870789/10000000000 : ℝ)^2103 ≤ (33316702183529/100000000000000 : ℝ)^1591 := by
    have hnat : (4353870789 : ℕ)^2103*100000000000000^1591 ≤ 33316702183529^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353870789 10000000000 33316702183529 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4227157117/10000000000 : ℝ)^2103 ≤ (32041065847689/100000000000000 : ℝ)^1591 := by
    have hnat : (4227157117 : ℕ)^2103*100000000000000^1591 ≤ 32041065847689^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227157117 10000000000 32041065847689 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22421477/50000000 : ℝ)^2103 ≤ (8660557986183/25000000000000 : ℝ)^1591 := by
    have hnat : (22421477 : ℕ)^2103*25000000000000^1591 ≤ 8660557986183^1591*50000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22421477 50000000 8660557986183 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353870789/10000000000 : ℝ), (4227157117/10000000000 : ℝ), (22421477/50000000 : ℝ)] ![(33316702183529/100000000000000 : ℝ), (32041065847689/100000000000000 : ℝ), (8660557986183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353870789/10000000000 : ℝ)|^2103 ≤ (33316702183529/100000000000000 : ℝ)^1591
        have hw : |(4353870789/10000000000 : ℝ)|=(4353870789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4227157117/10000000000 : ℝ)|^2103 ≤ (32041065847689/100000000000000 : ℝ)^1591
        have hw : |(4227157117/10000000000 : ℝ)|=(4227157117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(22421477/50000000 : ℝ)|^2103 ≤ (8660557986183/25000000000000 : ℝ)^1591
        have hw : |(22421477/50000000 : ℝ)|=(22421477/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s5_4 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-85219529/400000000 : ℝ)*x 0 + (526596587/1000000000 : ℝ)*x 1 + (2696316611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85219529/400000000 : ℝ)^2103 ≤ (6476597258171/50000000000000 : ℝ)^1591 := by
    have hnat : (85219529 : ℕ)^2103*50000000000000^1591 ≤ 6476597258171^1591*400000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85219529 400000000 6476597258171 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526596587/1000000000 : ℝ)^2103 ≤ (42839741077393/100000000000000 : ℝ)^1591 := by
    have hnat : (526596587 : ℕ)^2103*100000000000000^1591 ≤ 42839741077393^1591*1000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526596587 1000000000 42839741077393 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696316611/5000000000 : ℝ)^2103 ≤ (22103532195369/50000000000000 : ℝ)^1591 := by
    have hnat : (2696316611 : ℕ)^2103*50000000000000^1591 ≤ 22103532195369^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696316611 5000000000 22103532195369 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85219529/400000000 : ℝ), (526596587/1000000000 : ℝ), (2696316611/5000000000 : ℝ)] ![(6476597258171/50000000000000 : ℝ), (42839741077393/100000000000000 : ℝ), (22103532195369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85219529/400000000 : ℝ)|^2103 ≤ (6476597258171/50000000000000 : ℝ)^1591
        have hw : |(-85219529/400000000 : ℝ)|=(85219529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526596587/1000000000 : ℝ)|^2103 ≤ (42839741077393/100000000000000 : ℝ)^1591
        have hw : |(526596587/1000000000 : ℝ)|=(526596587/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696316611/5000000000 : ℝ)|^2103 ≤ (22103532195369/50000000000000 : ℝ)^1591
        have hw : |(2696316611/5000000000 : ℝ)|=(2696316611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s5_5 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312328771/10000000000 : ℝ)*x 0 + (-2068068651/10000000000 : ℝ)*x 1 + (215705327/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312328771/10000000000 : ℝ)^2103 ≤ (43338995685683/100000000000000 : ℝ)^1591 := by
    have hnat : (5312328771 : ℕ)^2103*100000000000000^1591 ≤ 43338995685683^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312328771 10000000000 43338995685683 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068068651/10000000000 : ℝ)^2103 ≤ (124539404173/1000000000000 : ℝ)^1591 := by
    have hnat : (2068068651 : ℕ)^2103*1000000000000^1591 ≤ 124539404173^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068068651 10000000000 124539404173 1000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215705327/400000000 : ℝ)^2103 ≤ (44207063881457/100000000000000 : ℝ)^1591 := by
    have hnat : (215705327 : ℕ)^2103*100000000000000^1591 ≤ 44207063881457^1591*400000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215705327 400000000 44207063881457 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312328771/10000000000 : ℝ), (-2068068651/10000000000 : ℝ), (215705327/400000000 : ℝ)] ![(43338995685683/100000000000000 : ℝ), (124539404173/1000000000000 : ℝ), (44207063881457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312328771/10000000000 : ℝ)|^2103 ≤ (43338995685683/100000000000000 : ℝ)^1591
        have hw : |(5312328771/10000000000 : ℝ)|=(5312328771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068068651/10000000000 : ℝ)|^2103 ≤ (124539404173/1000000000000 : ℝ)^1591
        have hw : |(-2068068651/10000000000 : ℝ)|=(2068068651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215705327/400000000 : ℝ)|^2103 ≤ (44207063881457/100000000000000 : ℝ)^1591
        have hw : |(215705327/400000000 : ℝ)|=(215705327/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s5_6 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312328577/10000000000 : ℝ)*x 0 + (2696316703/5000000000 : ℝ)*x 1 + (-10340343/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312328577/10000000000 : ℝ)^2103 ≤ (43338993593669/100000000000000 : ℝ)^1591 := by
    have hnat : (5312328577 : ℕ)^2103*100000000000000^1591 ≤ 43338993593669^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312328577 10000000000 43338993593669 100000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696316703/5000000000 : ℝ)^2103 ≤ (1105176659613/2500000000000 : ℝ)^1591 := by
    have hnat : (2696316703 : ℕ)^2103*2500000000000^1591 ≤ 1105176659613^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696316703 5000000000 1105176659613 2500000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10340343/50000000 : ℝ)^2103 ≤ (6226970005671/50000000000000 : ℝ)^1591 := by
    have hnat : (10340343 : ℕ)^2103*50000000000000^1591 ≤ 6226970005671^1591*50000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10340343 50000000 6226970005671 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312328577/10000000000 : ℝ), (2696316703/5000000000 : ℝ), (-10340343/50000000 : ℝ)] ![(43338993593669/100000000000000 : ℝ), (1105176659613/2500000000000 : ℝ), (6226970005671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312328577/10000000000 : ℝ)|^2103 ≤ (43338993593669/100000000000000 : ℝ)^1591
        have hw : |(5312328577/10000000000 : ℝ)|=(5312328577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696316703/5000000000 : ℝ)|^2103 ≤ (1105176659613/2500000000000 : ℝ)^1591
        have hw : |(2696316703/5000000000 : ℝ)|=(2696316703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-10340343/50000000 : ℝ)|^2103 ≤ (6226970005671/50000000000000 : ℝ)^1591
        have hw : |(-10340343/50000000 : ℝ)|=(10340343/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1219_s5_7 (p : ℝ) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4353881203/10000000000 : ℝ)*x 0 + (4483633999/10000000000 : ℝ)*x 1 + (2113910331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353881203/10000000000 : ℝ)^2103 ≤ (8329201879669/25000000000000 : ℝ)^1591 := by
    have hnat : (4353881203 : ℕ)^2103*25000000000000^1591 ≤ 8329201879669^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353881203 10000000000 8329201879669 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483633999/10000000000 : ℝ)^2103 ≤ (8658869586379/25000000000000 : ℝ)^1591 := by
    have hnat : (4483633999 : ℕ)^2103*25000000000000^1591 ≤ 8658869586379^1591*10000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483633999 10000000000 8658869586379 25000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2113910331/5000000000 : ℝ)^2103 ≤ (16023857061587/50000000000000 : ℝ)^1591 := by
    have hnat : (2113910331 : ℕ)^2103*50000000000000^1591 ≤ 16023857061587^1591*5000000000^2103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113910331 5000000000 16023857061587 50000000000000 2103 1591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2103/512 : ℝ)) 2103 1591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353881203/10000000000 : ℝ), (4483633999/10000000000 : ℝ), (2113910331/5000000000 : ℝ)] ![(8329201879669/25000000000000 : ℝ), (8658869586379/25000000000000 : ℝ), (16023857061587/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353881203/10000000000 : ℝ)|^2103 ≤ (8329201879669/25000000000000 : ℝ)^1591
        have hw : |(4353881203/10000000000 : ℝ)|=(4353881203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483633999/10000000000 : ℝ)|^2103 ≤ (8658869586379/25000000000000 : ℝ)^1591
        have hw : |(4483633999/10000000000 : ℝ)|=(4483633999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2113910331/5000000000 : ℝ)|^2103 ≤ (16023857061587/50000000000000 : ℝ)^1591
        have hw : |(2113910331/5000000000 : ℝ)|=(2113910331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1219_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11423/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14121/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5657/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5657/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5657/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5657/50000 : ℝ) ^ (8411/2048 : ℝ) ≤ (101403864070829/781250000000000000 : ℝ) := by
    have hpowers : (5657/50000 : ℝ)^8411 ≤ (101403864070829/781250000000000000 : ℝ)^2048 := by
      have hnat : (5657 : ℕ)^8411*781250000000000000^2048 ≤ 101403864070829^2048*50000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5657 50000 101403864070829 781250000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5657/50000 : ℝ)) (X := (101403864070829/781250000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8411/2048 : ℝ) ≤ (8333652102702743/25000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8411 ≤ (8333652102702743/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8411*25000000000000000000^2048 ≤ 8333652102702743^2048*20000^8411 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 8333652102702743 25000000000000000000 8411 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (8333652102702743/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (390726403864070829/390625000000000000 : ℝ) ≤ (10000632024842307/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (390726403864070829/390625000000000000 : ℝ)^2048 ≤ (10000632024842307/10000000000000000 : ℝ)^8411 := by
      have hnat : (390726403864070829 : ℕ)^2048*10000000000000000^8411 ≤ 10000632024842307^8411*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390726403864070829 390625000000000000 10000632024842307 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000632024842307/10000000000000000 : ℝ)) (X := (390726403864070829/390625000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011578575752969271/25000000000000000000 : ℝ) ≤ (10001127512547653/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (25011578575752969271/25000000000000000000 : ℝ)^2048 ≤ (10001127512547653/10000000000000000 : ℝ)^8411 := by
      have hnat : (25011578575752969271 : ℕ)^2048*10000000000000000^8411 ≤ 10001127512547653^8411*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011578575752969271 25000000000000000000 10001127512547653 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001127512547653/10000000000000000 : ℝ)) (X := (25011578575752969271/25000000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508333652102702743/12500000000000000000 : ℝ) ≤ (10001623000252999/10000000000000000 : ℝ) ^ (8411/2048 : ℝ) := by
    have hpowers : (12508333652102702743/12500000000000000000 : ℝ)^2048 ≤ (10001623000252999/10000000000000000 : ℝ)^8411 := by
      have hnat : (12508333652102702743 : ℕ)^2048*10000000000000000^8411 ≤ 10001623000252999^8411*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508333652102702743 12500000000000000000 10001623000252999 10000000000000000 2048 8411 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001623000252999/10000000000000000 : ℝ)) (X := (12508333652102702743/12500000000000000000 : ℝ)) (by norm_num) 8411 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(101403864070829/781250000000000000 : ℝ) ≤ ((29200634248767809459/29210000000000000000 : ℝ)+2*(247743852673/146050000000000 : ℝ)*(5657/50000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (29200634248767809459/29210000000000000000 : ℝ)+2*(247743852673/146050000000000 : ℝ)*(5657/50000 : ℝ)=(10000632024842307/10000000000000000 : ℝ) by norm_num, show 1+2*(101403864070829/781250000000000000 : ℝ)=(390726403864070829/390625000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8333652102702743/25000000000000000000 : ℝ)+(101403864070829/781250000000000000 : ℝ) ≤ ((29200634248767809459/29210000000000000000 : ℝ)+(247743852673/146050000000000 : ℝ)*((2847/20000 : ℝ)+(5657/50000 : ℝ)))^(8411/2048 : ℝ) := by
    rw [show (29200634248767809459/29210000000000000000 : ℝ)+(247743852673/146050000000000 : ℝ)*((2847/20000 : ℝ)+(5657/50000 : ℝ))=(10001127512547653/10000000000000000 : ℝ) by norm_num, show 1+(8333652102702743/25000000000000000000 : ℝ)+(101403864070829/781250000000000000 : ℝ)=(25011578575752969271/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8333652102702743/25000000000000000000 : ℝ) ≤ ((29200634248767809459/29210000000000000000 : ℝ)+2*(247743852673/146050000000000 : ℝ)*(2847/20000 : ℝ))^(8411/2048 : ℝ) := by
    rw [show (29200634248767809459/29210000000000000000 : ℝ)+2*(247743852673/146050000000000 : ℝ)*(2847/20000 : ℝ)=(10001623000252999/10000000000000000 : ℝ) by norm_num, show 1+2*(8333652102702743/25000000000000000000 : ℝ)=(12508333652102702743/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29200634248767809459/29210000000000000000 : ℝ)*(X 1 0+X 2 0)+(247743852673/146050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (29200634248767809459/29210000000000000000 : ℝ)) (alpha := (247743852673/146050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29200634248767809459/29210000000000000000 : ℝ)*(X 0 1+X 2 1)+(247743852673/146050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (29200634248767809459/29210000000000000000 : ℝ)) (alpha := (247743852673/146050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29200634248767809459/29210000000000000000 : ℝ)*(X 0 2+X 1 2)+(247743852673/146050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8411/2048 : ℝ)) (lo := (5657/50000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (29200634248767809459/29210000000000000000 : ℝ)) (alpha := (247743852673/146050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2130483183/10000000000 : ℝ)*X 0 0+(1348240509/2500000000 : ℝ)*X 0 1+(1316409573/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344764499/10000000000 : ℝ)*X 1 0+(-2195063709/10000000000 : ℝ)*X 1 1+(2632819151/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336191127/2500000000 : ℝ)*X 2 0+(2632819177/5000000000 : ℝ)*X 2 1+(-548765907/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353870789/10000000000 : ℝ)*X 0 0+(4227157117/10000000000 : ℝ)*X 0 1+(22421477/50000000 : ℝ)*X 0 2+(4353870789/10000000000 : ℝ)*X 1 0+(4227157117/10000000000 : ℝ)*X 1 1+(22421477/50000000 : ℝ)*X 1 2+(4353870789/10000000000 : ℝ)*X 2 0+(4227157117/10000000000 : ℝ)*X 2 1+(22421477/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85219529/400000000 : ℝ)*X 0 0+(526596587/1000000000 : ℝ)*X 0 1+(2696316611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312328771/10000000000 : ℝ)*X 1 0+(-2068068651/10000000000 : ℝ)*X 1 1+(215705327/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312328577/10000000000 : ℝ)*X 2 0+(2696316703/5000000000 : ℝ)*X 2 1+(-10340343/50000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353881203/10000000000 : ℝ)*X 0 0+(4483633999/10000000000 : ℝ)*X 0 1+(2113910331/5000000000 : ℝ)*X 0 2+(4353881203/10000000000 : ℝ)*X 1 0+(4483633999/10000000000 : ℝ)*X 1 1+(2113910331/5000000000 : ℝ)*X 1 2+(4353881203/10000000000 : ℝ)*X 2 0+(4483633999/10000000000 : ℝ)*X 2 1+(2113910331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1219_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14898917556713721086490916197/1460500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1028846853/50000000000000 : ℝ)*(base19) + (1006214753/50000000000000 : ℝ)*(base23) + (15630677/50000000000000 : ℝ)*(lower2) + (159802927/100000000000000 : ℝ)*(upper3) + (249153087/100000000000000 : ℝ)*(upper5) + (5871566417232339/100000000000000 : ℝ)*(major0) + (5871566417232339/100000000000000 : ℝ)*(major1) + (5871566417232339/100000000000000 : ℝ)*(major2) + (7854053536033801/100000000000000 : ℝ)*(sp0) + (490882264003763/6250000000000 : ℝ)*(sp1) + (981764533665551/12500000000000 : ℝ)*(sp2) + (486123345331121/12500000000000 : ℝ)*(sp3) + (64745720113/100000000000000 : ℝ)*(sp4) + (2745002031/10000000000000 : ℝ)*(sp7) + (1944507106334639/50000000000000 : ℝ)*(f.failure) + (3927059140876957/50000000000000 : ℝ)*(f.sum) + (4606871352369/3651250000000000000000000000 : ℝ)*base66 + (362257483252943713/127000000000000000000000000000000 : ℝ)*base68 + (36300608885056287/127000000000000000000000000000000 : ℝ)*base69 + (18409730766943713/127000000000000000000000000000000 : ℝ)*base72 + (15374803124131/3651250000000000000000000000 : ℝ)*base73 + (1665763334459056287/127000000000000000000000000000000 : ℝ)*base75 + (532826724289056287/127000000000000000000000000000000 : ℝ)*base77 + (146146086425056287/127000000000000000000000000000000 : ℝ)*base79 + (8676144360857/7302500000000000000000000000 : ℝ)*base81 + (6370831/5000000000000000000000 : ℝ)*base90 + (6370831/5000000000000000000000 : ℝ)*base92 + (6370831/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135989478949455540687531/14605000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2432783131/100000000000000 : ℝ)*(base19) + (243366037/10000000000000 : ℝ)*(base23) + (313745937/100000000000000 : ℝ)*(upper3) + (115169327/100000000000000 : ℝ)*(lower4) + (207739209/100000000000000 : ℝ)*(upper5) + (2950945923724309/50000000000000 : ℝ)*(major0) + (2950945923724309/50000000000000 : ℝ)*(major1) + (2950945923724309/50000000000000 : ℝ)*(major2) + (6063406057/10000000000000 : ℝ)*(sp1) + (36244448841/50000000000000 : ℝ)*(sp2) + (1973670803776277/25000000000000 : ℝ)*(sp4) + (7894620148261407/100000000000000 : ℝ)*(sp5) + (493413018284191/6250000000000 : ℝ)*(sp6) + (3909100169420153/100000000000000 : ℝ)*(sp7) + (3909100169420153/100000000000000 : ℝ)*(f.failure) + (1973670803776277/25000000000000 : ℝ)*(f.sum) + (14602266176633/14605000000000000000000000000 : ℝ)*base65 + (8037267677115703/63500000000000000000000000000000 : ℝ)*base68 + (618516962069615703/63500000000000000000000000000000 : ℝ)*base70 + (95779931406384297/63500000000000000000000000000000 : ℝ)*base71 + (8042490859257/3651250000000000000000000000 : ℝ)*base73 + (174113444728884297/63500000000000000000000000000000 : ℝ)*base75 + (140207946947115703/63500000000000000000000000000000 : ℝ)*base78 + (541695935368884297/63500000000000000000000000000000 : ℝ)*base79 + (10809933214561/7302500000000000000000000000 : ℝ)*base82 + (27504537/10000000000000000000000 : ℝ)*base90 + (27504537/10000000000000000000000 : ℝ)*base92 + (27504537/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1219_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5657/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1219_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1219_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4071/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1881/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1219_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1219_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1219_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8411/2048 : ℝ) ≤ p) (hpb : p ≤ (2103/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150978271/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4071/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1881/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11423/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14121/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1219_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
