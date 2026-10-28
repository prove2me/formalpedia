-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1080_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:49:01.771061+00:00
-- url     : https://prove2.me/submissions/77a5ea29-6482-40a7-8a09-61dab6a90535

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
theorem support_rectangle_w1080_s6_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196846341/10000000000 : ℝ)*x 0 + (1348658117/2500000000 : ℝ)*x 1 + (1316054419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196846341/10000000000 : ℝ)^8273 ≤ (2668605736587/20000000000000 : ℝ)^6225 := by
    have hnat : (2196846341 : ℕ)^8273*20000000000000^6225 ≤ 2668605736587^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196846341 10000000000 2668605736587 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348658117/2500000000 : ℝ)^8273 ≤ (44033011725503/100000000000000 : ℝ)^6225 := by
    have hnat : (1348658117 : ℕ)^8273*100000000000000^6225 ≤ 44033011725503^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348658117 2500000000 44033011725503 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316054419/2500000000 : ℝ)^8273 ≤ (21311979789691/50000000000000 : ℝ)^6225 := by
    have hnat : (1316054419 : ℕ)^8273*50000000000000^6225 ≤ 21311979789691^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316054419 2500000000 21311979789691 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196846341/10000000000 : ℝ), (1348658117/2500000000 : ℝ), (1316054419/2500000000 : ℝ)] ![(2668605736587/20000000000000 : ℝ), (44033011725503/100000000000000 : ℝ), (21311979789691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196846341/10000000000 : ℝ)|^8273 ≤ (2668605736587/20000000000000 : ℝ)^6225
        have hw : |(-2196846341/10000000000 : ℝ)|=(2196846341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348658117/2500000000 : ℝ)|^8273 ≤ (44033011725503/100000000000000 : ℝ)^6225
        have hw : |(1348658117/2500000000 : ℝ)|=(1348658117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316054419/2500000000 : ℝ)|^8273 ≤ (21311979789691/50000000000000 : ℝ)^6225
        have hw : |(1316054419/2500000000 : ℝ)|=(1316054419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s6_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345075621/10000000000 : ℝ)*x 0 + (-2263018409/10000000000 : ℝ)*x 1 + (526421771/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345075621/10000000000 : ℝ)^8273 ≤ (21748122407001/50000000000000 : ℝ)^6225 := by
    have hnat : (5345075621 : ℕ)^8273*50000000000000^6225 ≤ 21748122407001^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345075621 10000000000 21748122407001 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263018409/10000000000 : ℝ)^8273 ≤ (433743600971/3125000000000 : ℝ)^6225 := by
    have hnat : (2263018409 : ℕ)^8273*3125000000000^6225 ≤ 433743600971^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263018409 10000000000 433743600971 3125000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526421771/1000000000 : ℝ)^8273 ≤ (1331998748289/3125000000000 : ℝ)^6225 := by
    have hnat : (526421771 : ℕ)^8273*3125000000000^6225 ≤ 1331998748289^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526421771 1000000000 1331998748289 3125000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345075621/10000000000 : ℝ), (-2263018409/10000000000 : ℝ), (526421771/1000000000 : ℝ)] ![(21748122407001/50000000000000 : ℝ), (433743600971/3125000000000 : ℝ), (1331998748289/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345075621/10000000000 : ℝ)|^8273 ≤ (21748122407001/50000000000000 : ℝ)^6225
        have hw : |(5345075621/10000000000 : ℝ)|=(5345075621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2263018409/10000000000 : ℝ)|^8273 ≤ (433743600971/3125000000000 : ℝ)^6225
        have hw : |(-2263018409/10000000000 : ℝ)|=(2263018409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526421771/1000000000 : ℝ)|^8273 ≤ (1331998748289/3125000000000 : ℝ)^6225
        have hw : |(526421771/1000000000 : ℝ)|=(526421771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s6_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345075693/10000000000 : ℝ)*x 0 + (5264217691/10000000000 : ℝ)*x 1 + (-2263018339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345075693/10000000000 : ℝ)^8273 ≤ (21748122796337/50000000000000 : ℝ)^6225 := by
    have hnat : (5345075693 : ℕ)^8273*50000000000000^6225 ≤ 21748122796337^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345075693 10000000000 21748122796337 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264217691/10000000000 : ℝ)^8273 ≤ (21311979870397/50000000000000 : ℝ)^6225 := by
    have hnat : (5264217691 : ℕ)^8273*50000000000000^6225 ≤ 21311979870397^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264217691 10000000000 21311979870397 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2263018339/10000000000 : ℝ)^8273 ≤ (3469948665123/25000000000000 : ℝ)^6225 := by
    have hnat : (2263018339 : ℕ)^8273*25000000000000^6225 ≤ 3469948665123^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263018339 10000000000 3469948665123 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345075693/10000000000 : ℝ), (5264217691/10000000000 : ℝ), (-2263018339/10000000000 : ℝ)] ![(21748122796337/50000000000000 : ℝ), (21311979870397/50000000000000 : ℝ), (3469948665123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345075693/10000000000 : ℝ)|^8273 ≤ (21748122796337/50000000000000 : ℝ)^6225
        have hw : |(5345075693/10000000000 : ℝ)|=(5345075693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264217691/10000000000 : ℝ)|^8273 ≤ (21311979870397/50000000000000 : ℝ)^6225
        have hw : |(5264217691/10000000000 : ℝ)|=(5264217691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2263018339/10000000000 : ℝ)|^8273 ≤ (3469948665123/25000000000000 : ℝ)^6225
        have hw : |(-2263018339/10000000000 : ℝ)|=(2263018339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s6_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2186728539/5000000000 : ℝ)*x 0 + (4247199811/10000000000 : ℝ)*x 1 + (562938143/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186728539/5000000000 : ℝ)^8273 ≤ (8329092812873/25000000000000 : ℝ)^6225 := by
    have hnat : (2186728539 : ℕ)^8273*25000000000000^6225 ≤ 8329092812873^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186728539 5000000000 8329092812873 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247199811/10000000000 : ℝ)^8273 ≤ (32044239762521/100000000000000 : ℝ)^6225 := by
    have hnat : (4247199811 : ℕ)^8273*100000000000000^6225 ≤ 32044239762521^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247199811 10000000000 32044239762521 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562938143/1250000000 : ℝ)^8273 ≤ (34639388978593/100000000000000 : ℝ)^6225 := by
    have hnat : (562938143 : ℕ)^8273*100000000000000^6225 ≤ 34639388978593^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562938143 1250000000 34639388978593 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186728539/5000000000 : ℝ), (4247199811/10000000000 : ℝ), (562938143/1250000000 : ℝ)] ![(8329092812873/25000000000000 : ℝ), (32044239762521/100000000000000 : ℝ), (34639388978593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186728539/5000000000 : ℝ)|^8273 ≤ (8329092812873/25000000000000 : ℝ)^6225
        have hw : |(2186728539/5000000000 : ℝ)|=(2186728539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247199811/10000000000 : ℝ)|^8273 ≤ (32044239762521/100000000000000 : ℝ)^6225
        have hw : |(4247199811/10000000000 : ℝ)|=(4247199811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562938143/1250000000 : ℝ)|^8273 ≤ (34639388978593/100000000000000 : ℝ)^6225
        have hw : |(562938143/1250000000 : ℝ)|=(562938143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s6_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-439370251/2000000000 : ℝ)*x 0 + (526454717/1000000000 : ℝ)*x 1 + (5267873/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (439370251/2000000000 : ℝ)^8273 ≤ (13343068348507/100000000000000 : ℝ)^6225 := by
    have hnat : (439370251 : ℕ)^8273*100000000000000^6225 ≤ 13343068348507^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439370251 2000000000 13343068348507 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526454717/1000000000 : ℝ)^8273 ≤ (42627505227257/100000000000000 : ℝ)^6225 := by
    have hnat : (526454717 : ℕ)^8273*100000000000000^6225 ≤ 42627505227257^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526454717 1000000000 42627505227257 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5267873/9765625 : ℝ)^8273 ≤ (22014713201163/50000000000000 : ℝ)^6225 := by
    have hnat : (5267873 : ℕ)^8273*50000000000000^6225 ≤ 22014713201163^6225*9765625^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267873 9765625 22014713201163 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-439370251/2000000000 : ℝ), (526454717/1000000000 : ℝ), (5267873/9765625 : ℝ)] ![(13343068348507/100000000000000 : ℝ), (42627505227257/100000000000000 : ℝ), (22014713201163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-439370251/2000000000 : ℝ)|^8273 ≤ (13343068348507/100000000000000 : ℝ)^6225
        have hw : |(-439370251/2000000000 : ℝ)|=(439370251/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526454717/1000000000 : ℝ)|^8273 ≤ (42627505227257/100000000000000 : ℝ)^6225
        have hw : |(526454717/1000000000 : ℝ)|=(526454717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5267873/9765625 : ℝ)|^8273 ≤ (22014713201163/50000000000000 : ℝ)^6225
        have hw : |(5267873/9765625 : ℝ)|=(5267873/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s6_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656095083/5000000000 : ℝ)*x 0 + (-2132934461/10000000000 : ℝ)*x 1 + (2697150979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656095083/5000000000 : ℝ)^8273 ≤ (21570476554523/50000000000000 : ℝ)^6225 := by
    have hnat : (2656095083 : ℕ)^8273*50000000000000^6225 ≤ 21570476554523^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656095083 5000000000 21570476554523 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2132934461/10000000000 : ℝ)^8273 ≤ (1603702550971/12500000000000 : ℝ)^6225 := by
    have hnat : (2132934461 : ℕ)^8273*12500000000000^6225 ≤ 1603702550971^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132934461 10000000000 1603702550971 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697150979/5000000000 : ℝ)^8273 ≤ (44029426467411/100000000000000 : ℝ)^6225 := by
    have hnat : (2697150979 : ℕ)^8273*100000000000000^6225 ≤ 44029426467411^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697150979 5000000000 44029426467411 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656095083/5000000000 : ℝ), (-2132934461/10000000000 : ℝ), (2697150979/5000000000 : ℝ)] ![(21570476554523/50000000000000 : ℝ), (1603702550971/12500000000000 : ℝ), (44029426467411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656095083/5000000000 : ℝ)|^8273 ≤ (21570476554523/50000000000000 : ℝ)^6225
        have hw : |(2656095083/5000000000 : ℝ)|=(2656095083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2132934461/10000000000 : ℝ)|^8273 ≤ (1603702550971/12500000000000 : ℝ)^6225
        have hw : |(-2132934461/10000000000 : ℝ)|=(2132934461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697150979/5000000000 : ℝ)|^8273 ≤ (44029426467411/100000000000000 : ℝ)^6225
        have hw : |(2697150979/5000000000 : ℝ)|=(2697150979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s6_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312190339/10000000000 : ℝ)*x 0 + (5394301863/10000000000 : ℝ)*x 1 + (-2132934357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312190339/10000000000 : ℝ)^8273 ≤ (1725638199049/4000000000000 : ℝ)^6225 := by
    have hnat : (5312190339 : ℕ)^8273*4000000000000^6225 ≤ 1725638199049^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312190339 10000000000 1725638199049 4000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394301863/10000000000 : ℝ)^8273 ≤ (22014712718447/50000000000000 : ℝ)^6225 := by
    have hnat : (5394301863 : ℕ)^8273*50000000000000^6225 ≤ 22014712718447^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394301863 10000000000 22014712718447 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132934357/10000000000 : ℝ)^8273 ≤ (32074048941/250000000000 : ℝ)^6225 := by
    have hnat : (2132934357 : ℕ)^8273*250000000000^6225 ≤ 32074048941^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132934357 10000000000 32074048941 250000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312190339/10000000000 : ℝ), (5394301863/10000000000 : ℝ), (-2132934357/10000000000 : ℝ)] ![(1725638199049/4000000000000 : ℝ), (22014712718447/50000000000000 : ℝ), (32074048941/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312190339/10000000000 : ℝ)|^8273 ≤ (1725638199049/4000000000000 : ℝ)^6225
        have hw : |(5312190339/10000000000 : ℝ)|=(5312190339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394301863/10000000000 : ℝ)|^8273 ≤ (22014712718447/50000000000000 : ℝ)^6225
        have hw : |(5394301863/10000000000 : ℝ)|=(5394301863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2132934357/10000000000 : ℝ)|^8273 ≤ (32074048941/250000000000 : ℝ)^6225
        have hw : |(-2132934357/10000000000 : ℝ)|=(2132934357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s6_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874693343/2000000000 : ℝ)*x 0 + (900571631/2000000000 : ℝ)*x 1 + (424784963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874693343/2000000000 : ℝ)^8273 ≤ (16658234408747/50000000000000 : ℝ)^6225 := by
    have hnat : (874693343 : ℕ)^8273*50000000000000^6225 ≤ 16658234408747^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874693343 2000000000 16658234408747 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900571631/2000000000 : ℝ)^8273 ≤ (6926555100277/20000000000000 : ℝ)^6225 := by
    have hnat : (900571631 : ℕ)^8273*20000000000000^6225 ≤ 6926555100277^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900571631 2000000000 6926555100277 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424784963/1000000000 : ℝ)^8273 ≤ (16025377830307/50000000000000 : ℝ)^6225 := by
    have hnat : (424784963 : ℕ)^8273*50000000000000^6225 ≤ 16025377830307^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424784963 1000000000 16025377830307 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874693343/2000000000 : ℝ), (900571631/2000000000 : ℝ), (424784963/1000000000 : ℝ)] ![(16658234408747/50000000000000 : ℝ), (6926555100277/20000000000000 : ℝ), (16025377830307/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874693343/2000000000 : ℝ)|^8273 ≤ (16658234408747/50000000000000 : ℝ)^6225
        have hw : |(874693343/2000000000 : ℝ)|=(874693343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900571631/2000000000 : ℝ)|^8273 ≤ (6926555100277/20000000000000 : ℝ)^6225
        have hw : |(900571631/2000000000 : ℝ)|=(900571631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424784963/1000000000 : ℝ)|^8273 ≤ (16025377830307/50000000000000 : ℝ)^6225
        have hw : |(424784963/1000000000 : ℝ)|=(424784963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (563/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (879/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (879/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11221/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (879/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (879/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11221/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (879/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (879/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11221/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11221/100000 : ℝ) ^ (517/128 : ℝ) ≤ (727759882718941/5000000000000000000 : ℝ) := by
    have hpowers : (11221/100000 : ℝ)^517 ≤ (727759882718941/5000000000000000000 : ℝ)^128 := by
      have hnat : (11221 : ℕ)^517*5000000000000000000^128 ≤ 727759882718941^128*100000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11221 100000 727759882718941 5000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11221/100000 : ℝ)) (X := (727759882718941/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (879/6250 : ℝ) ^ (517/128 : ℝ) ≤ (1811875854470111/5000000000000000000 : ℝ) := by
    have hpowers : (879/6250 : ℝ)^517 ≤ (1811875854470111/5000000000000000000 : ℝ)^128 := by
      have hnat : (879 : ℕ)^517*5000000000000000000^128 ≤ 1811875854470111^128*6250^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        879 6250 1811875854470111 5000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (879/6250 : ℝ)) (X := (1811875854470111/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500727759882718941/2500000000000000000 : ℝ) ≤ (10000720642668929/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (2500727759882718941/2500000000000000000 : ℝ)^128 ≤ (10000720642668929/10000000000000000 : ℝ)^517 := by
      have hnat : (2500727759882718941 : ℕ)^128*10000000000000000^517 ≤ 10000720642668929^517*2500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500727759882718941 2500000000000000000 10000720642668929 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000720642668929/10000000000000000 : ℝ)) (X := (2500727759882718941/2500000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (1250634908934297263/1250000000000000000 : ℝ) ≤ (2000251459400837/2000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (1250634908934297263/1250000000000000000 : ℝ)^128 ≤ (2000251459400837/2000000000000000 : ℝ)^517 := by
      have hnat : (1250634908934297263 : ℕ)^128*2000000000000000^517 ≤ 2000251459400837^517*1250000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250634908934297263 1250000000000000000 2000251459400837 2000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000251459400837/2000000000000000 : ℝ)) (X := (1250634908934297263/1250000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501811875854470111/2500000000000000000 : ℝ) ≤ (10001793951339441/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (2501811875854470111/2500000000000000000 : ℝ)^128 ≤ (10001793951339441/10000000000000000 : ℝ)^517 := by
      have hnat : (2501811875854470111 : ℕ)^128*10000000000000000^517 ≤ 10001793951339441^517*2500000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501811875854470111 2500000000000000000 10001793951339441 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001793951339441/10000000000000000 : ℝ)) (X := (2501811875854470111/2500000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(727759882718941/5000000000000000000 : ℝ) ≤ ((5684001038103189999/5686000000000000000 : ℝ)+2*(67081791907/35537500000000 : ℝ)*(11221/100000 : ℝ))^(517/128 : ℝ) := by
    rw [show (5684001038103189999/5686000000000000000 : ℝ)+2*(67081791907/35537500000000 : ℝ)*(11221/100000 : ℝ)=(10000720642668929/10000000000000000 : ℝ) by norm_num, show 1+2*(727759882718941/5000000000000000000 : ℝ)=(2500727759882718941/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1811875854470111/5000000000000000000 : ℝ)+(727759882718941/5000000000000000000 : ℝ) ≤ ((5684001038103189999/5686000000000000000 : ℝ)+(67081791907/35537500000000 : ℝ)*((879/6250 : ℝ)+(11221/100000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (5684001038103189999/5686000000000000000 : ℝ)+(67081791907/35537500000000 : ℝ)*((879/6250 : ℝ)+(11221/100000 : ℝ))=(2000251459400837/2000000000000000 : ℝ) by norm_num, show 1+(1811875854470111/5000000000000000000 : ℝ)+(727759882718941/5000000000000000000 : ℝ)=(1250634908934297263/1250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1811875854470111/5000000000000000000 : ℝ) ≤ ((5684001038103189999/5686000000000000000 : ℝ)+2*(67081791907/35537500000000 : ℝ)*(879/6250 : ℝ))^(517/128 : ℝ) := by
    rw [show (5684001038103189999/5686000000000000000 : ℝ)+2*(67081791907/35537500000000 : ℝ)*(879/6250 : ℝ)=(10001793951339441/10000000000000000 : ℝ) by norm_num, show 1+2*(1811875854470111/5000000000000000000 : ℝ)=(2501811875854470111/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5684001038103189999/5686000000000000000 : ℝ)*(X 1 0+X 2 0)+(67081791907/35537500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (5684001038103189999/5686000000000000000 : ℝ)) (alpha := (67081791907/35537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5684001038103189999/5686000000000000000 : ℝ)*(X 0 1+X 2 1)+(67081791907/35537500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (5684001038103189999/5686000000000000000 : ℝ)) (alpha := (67081791907/35537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5684001038103189999/5686000000000000000 : ℝ)*(X 0 2+X 1 2)+(67081791907/35537500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11221/100000 : ℝ)) (hi := (879/6250 : ℝ)) (c := (5684001038103189999/5686000000000000000 : ℝ)) (alpha := (67081791907/35537500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2196846341/10000000000 : ℝ)*X 0 0+(1348658117/2500000000 : ℝ)*X 0 1+(1316054419/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345075621/10000000000 : ℝ)*X 1 0+(-2263018409/10000000000 : ℝ)*X 1 1+(526421771/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345075693/10000000000 : ℝ)*X 2 0+(5264217691/10000000000 : ℝ)*X 2 1+(-2263018339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186728539/5000000000 : ℝ)*X 0 0+(4247199811/10000000000 : ℝ)*X 0 1+(562938143/1250000000 : ℝ)*X 0 2+(2186728539/5000000000 : ℝ)*X 1 0+(4247199811/10000000000 : ℝ)*X 1 1+(562938143/1250000000 : ℝ)*X 1 2+(2186728539/5000000000 : ℝ)*X 2 0+(4247199811/10000000000 : ℝ)*X 2 1+(562938143/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-439370251/2000000000 : ℝ)*X 0 0+(526454717/1000000000 : ℝ)*X 0 1+(5267873/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656095083/5000000000 : ℝ)*X 1 0+(-2132934461/10000000000 : ℝ)*X 1 1+(2697150979/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312190339/10000000000 : ℝ)*X 2 0+(5394301863/10000000000 : ℝ)*X 2 1+(-2132934357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874693343/2000000000 : ℝ)*X 0 0+(900571631/2000000000 : ℝ)*X 0 1+(424784963/1000000000 : ℝ)*X 0 2+(874693343/2000000000 : ℝ)*X 1 0+(900571631/2000000000 : ℝ)*X 1 1+(424784963/1000000000 : ℝ)*X 1 2+(874693343/2000000000 : ℝ)*X 2 0+(900571631/2000000000 : ℝ)*X 2 1+(424784963/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (584828208192740736683442477/71075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1989335919/100000000000000 : ℝ)*(base19) + (814429889/50000000000000 : ℝ)*(base23) + (247886431/100000000000000 : ℝ)*(lower2) + (148523529/50000000000000 : ℝ)*(upper3) + (10167763/12500000000000 : ℝ)*(upper5) + (1446199582448053/25000000000000 : ℝ)*(major0) + (1446199582448053/25000000000000 : ℝ)*(major1) + (1446199582448053/25000000000000 : ℝ)*(major2) + (7667895513909671/100000000000000 : ℝ)*(sp0) + (958493139565461/12500000000000 : ℝ)*(sp1) + (766794547699983/10000000000000 : ℝ)*(sp2) + (156064766762303/4000000000000 : ℝ)*(sp3) + (3224496871/6250000000000 : ℝ)*(sp4) + (15055194863/50000000000000 : ℝ)*(sp7) + (3901649279447301/100000000000000 : ℝ)*(f.failure) + (958493388232451/12500000000000 : ℝ)*(f.sum) + (89092077986263/14215000000000000000000000000 : ℝ)*base66 + (349465569761531947/142150000000000000000000000000000 : ℝ)*base67 + (1630951537694781947/142150000000000000000000000000000 : ℝ)*base69 + (1092279892513781947/142150000000000000000000000000000 : ℝ)*base71 + (79628569870273/14215000000000000000000000000 : ℝ)*base74 + (4359166150168981947/142150000000000000000000000000000 : ℝ)*base75 + (679999128458481947/142150000000000000000000000000000 : ℝ)*base77 + (1551526712510231947/142150000000000000000000000000000 : ℝ)*base79 + (17807473126061/7107500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6290969/5000000000000000000000 : ℝ)*base90 + (6290969/5000000000000000000000 : ℝ)*base92 + (6290969/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3724202900080162302091447521/284300000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (662464033/100000000000000 : ℝ)*(base19) + (795058351/50000000000000 : ℝ)*(base23) + (133160851/100000000000000 : ℝ)*(upper3) + (55291037/20000000000000 : ℝ)*(lower4) + (68409843/100000000000000 : ℝ)*(upper5) + (5814138307475831/100000000000000 : ℝ)*(major0) + (5814138307475831/100000000000000 : ℝ)*(major1) + (5814138307475831/100000000000000 : ℝ)*(major2) + (13573832631/100000000000000 : ℝ)*(sp1) + (4851758977/12500000000000 : ℝ)*(sp2) + (3853419042027619/50000000000000 : ℝ)*(sp4) + (3853411923879287/50000000000000 : ℝ)*(sp5) + (48167485499167/625000000000 : ℝ)*(sp6) + (1960719047122327/50000000000000 : ℝ)*(sp7) + (1960719047122327/50000000000000 : ℝ)*(f.failure) + (3853419042027619/50000000000000 : ℝ)*(f.sum) + (14419658035633/1776875000000000000000000000 : ℝ)*base66 + (554855386689865831/568600000000000000000000000000000 : ℝ)*base68 + (3748495521437465831/568600000000000000000000000000000 : ℝ)*base70 + (1381505350758865831/568600000000000000000000000000000 : ℝ)*base72 + (462820624181/14215000000000000000000000000 : ℝ)*base73 + (8244050865601065831/568600000000000000000000000000000 : ℝ)*base76 + (5596090477362665831/568600000000000000000000000000000 : ℝ)*base78 + (2535186699951465831/568600000000000000000000000000000 : ℝ)*base80 + (2300853865549/3553750000000000000000000000 : ℝ)*base81 + (16585037/2500000000000000000000 : ℝ)*base89 + (16585037/2500000000000000000000 : ℝ)*base91 + (16585037/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1080_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1080_s7_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196884253/10000000000 : ℝ)*x 0 + (1348550553/2500000000 : ℝ)*x 1 + (65807787/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196884253/10000000000 : ℝ)^8273 ≤ (13343334707533/100000000000000 : ℝ)^6225 := by
    have hnat : (2196884253 : ℕ)^8273*100000000000000^6225 ≤ 13343334707533^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196884253 10000000000 13343334707533 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348550553/2500000000 : ℝ)^8273 ≤ (44028344471521/100000000000000 : ℝ)^6225 := by
    have hnat : (1348550553 : ℕ)^8273*100000000000000^6225 ≤ 44028344471521^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348550553 2500000000 44028344471521 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65807787/125000000 : ℝ)^8273 ≤ (42628320805251/100000000000000 : ℝ)^6225 := by
    have hnat : (65807787 : ℕ)^8273*100000000000000^6225 ≤ 42628320805251^6225*125000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65807787 125000000 42628320805251 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196884253/10000000000 : ℝ), (1348550553/2500000000 : ℝ), (65807787/125000000 : ℝ)] ![(13343334707533/100000000000000 : ℝ), (44028344471521/100000000000000 : ℝ), (42628320805251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196884253/10000000000 : ℝ)|^8273 ≤ (13343334707533/100000000000000 : ℝ)^6225
        have hw : |(-2196884253/10000000000 : ℝ)|=(2196884253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348550553/2500000000 : ℝ)|^8273 ≤ (44028344471521/100000000000000 : ℝ)^6225
        have hw : |(1348550553/2500000000 : ℝ)|=(1348550553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65807787/125000000 : ℝ)|^8273 ≤ (42628320805251/100000000000000 : ℝ)^6225
        have hw : |(65807787/125000000 : ℝ)|=(65807787/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s7_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336241919/2500000000 : ℝ)*x 0 + (-565656811/2500000000 : ℝ)*x 1 + (2632311243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336241919/2500000000 : ℝ)^8273 ≤ (43495077405997/100000000000000 : ℝ)^6225 := by
    have hnat : (1336241919 : ℕ)^8273*100000000000000^6225 ≤ 43495077405997^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336241919 2500000000 43495077405997 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565656811/2500000000 : ℝ)^8273 ≤ (693830343947/5000000000000 : ℝ)^6225 := by
    have hnat : (565656811 : ℕ)^8273*5000000000000^6225 ≤ 693830343947^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565656811 2500000000 693830343947 5000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632311243/5000000000 : ℝ)^8273 ≤ (21314157852257/50000000000000 : ℝ)^6225 := by
    have hnat : (2632311243 : ℕ)^8273*50000000000000^6225 ≤ 21314157852257^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632311243 5000000000 21314157852257 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336241919/2500000000 : ℝ), (-565656811/2500000000 : ℝ), (2632311243/5000000000 : ℝ)] ![(43495077405997/100000000000000 : ℝ), (693830343947/5000000000000 : ℝ), (21314157852257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336241919/2500000000 : ℝ)|^8273 ≤ (43495077405997/100000000000000 : ℝ)^6225
        have hw : |(1336241919/2500000000 : ℝ)|=(1336241919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-565656811/2500000000 : ℝ)|^8273 ≤ (693830343947/5000000000000 : ℝ)^6225
        have hw : |(-565656811/2500000000 : ℝ)|=(565656811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632311243/5000000000 : ℝ)|^8273 ≤ (21314157852257/50000000000000 : ℝ)^6225
        have hw : |(2632311243/5000000000 : ℝ)|=(2632311243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s7_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668120949/1250000000 : ℝ)*x 0 + (5264622919/10000000000 : ℝ)*x 1 + (-70707087/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668120949/1250000000 : ℝ)^8273 ≤ (21747538248777/50000000000000 : ℝ)^6225 := by
    have hnat : (668120949 : ℕ)^8273*50000000000000^6225 ≤ 21747538248777^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668120949 1250000000 21747538248777 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264622919/10000000000 : ℝ)^8273 ≤ (2664270022753/6250000000000 : ℝ)^6225 := by
    have hnat : (5264622919 : ℕ)^8273*6250000000000^6225 ≤ 2664270022753^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264622919 10000000000 2664270022753 6250000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70707087/312500000 : ℝ)^8273 ≤ (6938301564813/50000000000000 : ℝ)^6225 := by
    have hnat : (70707087 : ℕ)^8273*50000000000000^6225 ≤ 6938301564813^6225*312500000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70707087 312500000 6938301564813 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668120949/1250000000 : ℝ), (5264622919/10000000000 : ℝ), (-70707087/312500000 : ℝ)] ![(21747538248777/50000000000000 : ℝ), (2664270022753/6250000000000 : ℝ), (6938301564813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668120949/1250000000 : ℝ)|^8273 ≤ (21747538248777/50000000000000 : ℝ)^6225
        have hw : |(668120949/1250000000 : ℝ)|=(668120949/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264622919/10000000000 : ℝ)|^8273 ≤ (2664270022753/6250000000000 : ℝ)^6225
        have hw : |(5264622919/10000000000 : ℝ)|=(5264622919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-70707087/312500000 : ℝ)|^8273 ≤ (6938301564813/50000000000000 : ℝ)^6225
        have hw : |(-70707087/312500000 : ℝ)|=(70707087/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s7_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (273342417/625000000 : ℝ)*x 0 + (849603337/2000000000 : ℝ)*x 1 + (450268243/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273342417/625000000 : ℝ)^8273 ≤ (33316589871519/100000000000000 : ℝ)^6225 := by
    have hnat : (273342417 : ℕ)^8273*100000000000000^6225 ≤ 33316589871519^6225*625000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273342417 625000000 33316589871519 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849603337/2000000000 : ℝ)^8273 ≤ (3205243081599/10000000000000 : ℝ)^6225 := by
    have hnat : (849603337 : ℕ)^8273*10000000000000^6225 ≤ 3205243081599^6225*2000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849603337 2000000000 3205243081599 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450268243/1000000000 : ℝ)^8273 ≤ (6926195861293/20000000000000 : ℝ)^6225 := by
    have hnat : (450268243 : ℕ)^8273*20000000000000^6225 ≤ 6926195861293^6225*1000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450268243 1000000000 6926195861293 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273342417/625000000 : ℝ), (849603337/2000000000 : ℝ), (450268243/1000000000 : ℝ)] ![(33316589871519/100000000000000 : ℝ), (3205243081599/10000000000000 : ℝ), (6926195861293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273342417/625000000 : ℝ)|^8273 ≤ (33316589871519/100000000000000 : ℝ)^6225
        have hw : |(273342417/625000000 : ℝ)|=(273342417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849603337/2000000000 : ℝ)|^8273 ≤ (3205243081599/10000000000000 : ℝ)^6225
        have hw : |(849603337/2000000000 : ℝ)|=(849603337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450268243/1000000000 : ℝ)|^8273 ≤ (6926195861293/20000000000000 : ℝ)^6225
        have hw : |(450268243/1000000000 : ℝ)|=(450268243/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s7_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549222383/2500000000 : ℝ)*x 0 + (2632473799/5000000000 : ℝ)*x 1 + (2696938113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549222383/2500000000 : ℝ)^8273 ≤ (1334337731961/10000000000000 : ℝ)^6225 := by
    have hnat : (549222383 : ℕ)^8273*10000000000000^6225 ≤ 1334337731961^6225*2500000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549222383 2500000000 1334337731961 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632473799/5000000000 : ℝ)^8273 ≤ (21315907143103/50000000000000 : ℝ)^6225 := by
    have hnat : (2632473799 : ℕ)^8273*50000000000000^6225 ≤ 21315907143103^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632473799 5000000000 21315907143103 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696938113/5000000000 : ℝ)^8273 ≤ (1100620209513/2500000000000 : ℝ)^6225 := by
    have hnat : (2696938113 : ℕ)^8273*2500000000000^6225 ≤ 1100620209513^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696938113 5000000000 1100620209513 2500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549222383/2500000000 : ℝ), (2632473799/5000000000 : ℝ), (2696938113/5000000000 : ℝ)] ![(1334337731961/10000000000000 : ℝ), (21315907143103/50000000000000 : ℝ), (1100620209513/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549222383/2500000000 : ℝ)|^8273 ≤ (1334337731961/10000000000000 : ℝ)^6225
        have hw : |(-549222383/2500000000 : ℝ)|=(549222383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632473799/5000000000 : ℝ)|^8273 ≤ (21315907143103/50000000000000 : ℝ)^6225
        have hw : |(2632473799/5000000000 : ℝ)|=(2632473799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696938113/5000000000 : ℝ)|^8273 ≤ (1100620209513/2500000000000 : ℝ)^6225
        have hw : |(2696938113/5000000000 : ℝ)|=(2696938113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s7_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312293143/10000000000 : ℝ)*x 0 + (-266671639/1250000000 : ℝ)*x 1 + (2696938113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312293143/10000000000 : ℝ)^8273 ≤ (8628412907449/20000000000000 : ℝ)^6225 := by
    have hnat : (5312293143 : ℕ)^8273*20000000000000^6225 ≤ 8628412907449^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312293143 10000000000 8628412907449 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (266671639/1250000000 : ℝ)^8273 ≤ (6416563534369/50000000000000 : ℝ)^6225 := by
    have hnat : (266671639 : ℕ)^8273*50000000000000^6225 ≤ 6416563534369^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266671639 1250000000 6416563534369 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696938113/5000000000 : ℝ)^8273 ≤ (1100620209513/2500000000000 : ℝ)^6225 := by
    have hnat : (2696938113 : ℕ)^8273*2500000000000^6225 ≤ 1100620209513^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696938113 5000000000 1100620209513 2500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312293143/10000000000 : ℝ), (-266671639/1250000000 : ℝ), (2696938113/5000000000 : ℝ)] ![(8628412907449/20000000000000 : ℝ), (6416563534369/50000000000000 : ℝ), (1100620209513/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312293143/10000000000 : ℝ)|^8273 ≤ (8628412907449/20000000000000 : ℝ)^6225
        have hw : |(5312293143/10000000000 : ℝ)|=(5312293143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-266671639/1250000000 : ℝ)|^8273 ≤ (6416563534369/50000000000000 : ℝ)^6225
        have hw : |(-266671639/1250000000 : ℝ)|=(266671639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696938113/5000000000 : ℝ)|^8273 ≤ (1100620209513/2500000000000 : ℝ)^6225
        have hw : |(2696938113/5000000000 : ℝ)|=(2696938113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s7_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664036643/1250000000 : ℝ)*x 0 + (215755049/400000000 : ℝ)*x 1 + (-2133373111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664036643/1250000000 : ℝ)^8273 ≤ (21571032274019/50000000000000 : ℝ)^6225 := by
    have hnat : (664036643 : ℕ)^8273*50000000000000^6225 ≤ 21571032274019^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664036643 1250000000 21571032274019 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215755049/400000000 : ℝ)^8273 ≤ (44024808369673/100000000000000 : ℝ)^6225 := by
    have hnat : (215755049 : ℕ)^8273*100000000000000^6225 ≤ 44024808369673^6225*400000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215755049 400000000 44024808369673 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133373111/10000000000 : ℝ)^8273 ≤ (1604140882593/12500000000000 : ℝ)^6225 := by
    have hnat : (2133373111 : ℕ)^8273*12500000000000^6225 ≤ 1604140882593^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133373111 10000000000 1604140882593 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664036643/1250000000 : ℝ), (215755049/400000000 : ℝ), (-2133373111/10000000000 : ℝ)] ![(21571032274019/50000000000000 : ℝ), (44024808369673/100000000000000 : ℝ), (1604140882593/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664036643/1250000000 : ℝ)|^8273 ≤ (21571032274019/50000000000000 : ℝ)^6225
        have hw : |(664036643/1250000000 : ℝ)|=(664036643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215755049/400000000 : ℝ)|^8273 ≤ (44024808369673/100000000000000 : ℝ)^6225
        have hw : |(215755049/400000000 : ℝ)|=(215755049/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2133373111/10000000000 : ℝ)|^8273 ≤ (1604140882593/12500000000000 : ℝ)^6225
        have hw : |(-2133373111/10000000000 : ℝ)|=(2133373111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s7_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373488073/10000000000 : ℝ)*x 0 + (562755411/1250000000 : ℝ)*x 1 + (531082333/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373488073/10000000000 : ℝ)^8273 ≤ (16658342524193/50000000000000 : ℝ)^6225 := by
    have hnat : (4373488073 : ℕ)^8273*50000000000000^6225 ≤ 16658342524193^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373488073 10000000000 16658342524193 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562755411/1250000000 : ℝ)^8273 ≤ (6924889286319/20000000000000 : ℝ)^6225 := by
    have hnat : (562755411 : ℕ)^8273*20000000000000^6225 ≤ 6924889286319^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562755411 1250000000 6924889286319 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531082333/1250000000 : ℝ)^8273 ≤ (6411773701151/20000000000000 : ℝ)^6225 := by
    have hnat : (531082333 : ℕ)^8273*20000000000000^6225 ≤ 6411773701151^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531082333 1250000000 6411773701151 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373488073/10000000000 : ℝ), (562755411/1250000000 : ℝ), (531082333/1250000000 : ℝ)] ![(16658342524193/50000000000000 : ℝ), (6924889286319/20000000000000 : ℝ), (6411773701151/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373488073/10000000000 : ℝ)|^8273 ≤ (16658342524193/50000000000000 : ℝ)^6225
        have hw : |(4373488073/10000000000 : ℝ)|=(4373488073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562755411/1250000000 : ℝ)|^8273 ≤ (6924889286319/20000000000000 : ℝ)^6225
        have hw : |(562755411/1250000000 : ℝ)|=(562755411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531082333/1250000000 : ℝ)|^8273 ≤ (6411773701151/20000000000000 : ℝ)^6225
        have hw : |(531082333/1250000000 : ℝ)|=(531082333/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (11269/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7007/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14023/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (563/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14023/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (563/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14023/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (563/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (563/5000 : ℝ) ^ (517/128 : ℝ) ≤ (7380304572436207/50000000000000000000 : ℝ) := by
    have hpowers : (563/5000 : ℝ)^517 ≤ (7380304572436207/50000000000000000000 : ℝ)^128 := by
      have hnat : (563 : ℕ)^517*50000000000000000000^128 ≤ 7380304572436207^128*5000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        563 5000 7380304572436207 50000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (563/5000 : ℝ)) (X := (7380304572436207/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14023/100000 : ℝ) ^ (517/128 : ℝ) ≤ (35812711993410853/100000000000000000000 : ℝ) := by
    have hpowers : (14023/100000 : ℝ)^517 ≤ (35812711993410853/100000000000000000000 : ℝ)^128 := by
      have hnat : (14023 : ℕ)^517*100000000000000000000^128 ≤ 35812711993410853^128*100000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14023 100000 35812711993410853 100000000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14023/100000 : ℝ)) (X := (35812711993410853/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007380304572436207/25000000000000000000 : ℝ) ≤ (1000073081167191/1000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (25007380304572436207/25000000000000000000 : ℝ)^128 ≤ (1000073081167191/1000000000000000 : ℝ)^517 := by
      have hnat : (25007380304572436207 : ℕ)^128*1000000000000000^517 ≤ 1000073081167191^517*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007380304572436207 25000000000000000000 1000073081167191 1000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000073081167191/1000000000000000 : ℝ)) (X := (25007380304572436207/25000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050573321138283267/100000000000000000000 : ℝ) ≤ (625078241704963/625000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (100050573321138283267/100000000000000000000 : ℝ)^128 ≤ (625078241704963/625000000000000 : ℝ)^517 := by
      have hnat : (100050573321138283267 : ℕ)^128*625000000000000^517 ≤ 625078241704963^517*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050573321138283267 100000000000000000000 625078241704963 625000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625078241704963/625000000000000 : ℝ)) (X := (100050573321138283267/100000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035812711993410853/50000000000000000000 : ℝ) ≤ (5000886461443453/5000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (50035812711993410853/50000000000000000000 : ℝ)^128 ≤ (5000886461443453/5000000000000000 : ℝ)^517 := by
      have hnat : (50035812711993410853 : ℕ)^128*5000000000000000^517 ≤ 5000886461443453^517*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035812711993410853 50000000000000000000 5000886461443453 5000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000886461443453/5000000000000000 : ℝ)) (X := (50035812711993410853/50000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7380304572436207/50000000000000000000 : ℝ) ≤ ((2762028506036863237/2763000000000000000 : ℝ)+2*(260527803749/138150000000000 : ℝ)*(563/5000 : ℝ))^(517/128 : ℝ) := by
    rw [show (2762028506036863237/2763000000000000000 : ℝ)+2*(260527803749/138150000000000 : ℝ)*(563/5000 : ℝ)=(1000073081167191/1000000000000000 : ℝ) by norm_num, show 1+2*(7380304572436207/50000000000000000000 : ℝ)=(25007380304572436207/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35812711993410853/100000000000000000000 : ℝ)+(7380304572436207/50000000000000000000 : ℝ) ≤ ((2762028506036863237/2763000000000000000 : ℝ)+(260527803749/138150000000000 : ℝ)*((14023/100000 : ℝ)+(563/5000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (2762028506036863237/2763000000000000000 : ℝ)+(260527803749/138150000000000 : ℝ)*((14023/100000 : ℝ)+(563/5000 : ℝ))=(625078241704963/625000000000000 : ℝ) by norm_num, show 1+(35812711993410853/100000000000000000000 : ℝ)+(7380304572436207/50000000000000000000 : ℝ)=(100050573321138283267/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35812711993410853/100000000000000000000 : ℝ) ≤ ((2762028506036863237/2763000000000000000 : ℝ)+2*(260527803749/138150000000000 : ℝ)*(14023/100000 : ℝ))^(517/128 : ℝ) := by
    rw [show (2762028506036863237/2763000000000000000 : ℝ)+2*(260527803749/138150000000000 : ℝ)*(14023/100000 : ℝ)=(5000886461443453/5000000000000000 : ℝ) by norm_num, show 1+2*(35812711993410853/100000000000000000000 : ℝ)=(50035812711993410853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2762028506036863237/2763000000000000000 : ℝ)*(X 1 0+X 2 0)+(260527803749/138150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (2762028506036863237/2763000000000000000 : ℝ)) (alpha := (260527803749/138150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2762028506036863237/2763000000000000000 : ℝ)*(X 0 1+X 2 1)+(260527803749/138150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (2762028506036863237/2763000000000000000 : ℝ)) (alpha := (260527803749/138150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2762028506036863237/2763000000000000000 : ℝ)*(X 0 2+X 1 2)+(260527803749/138150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (563/5000 : ℝ)) (hi := (14023/100000 : ℝ)) (c := (2762028506036863237/2763000000000000000 : ℝ)) (alpha := (260527803749/138150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2196884253/10000000000 : ℝ)*X 0 0+(1348550553/2500000000 : ℝ)*X 0 1+(65807787/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336241919/2500000000 : ℝ)*X 1 0+(-565656811/2500000000 : ℝ)*X 1 1+(2632311243/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668120949/1250000000 : ℝ)*X 2 0+(5264622919/10000000000 : ℝ)*X 2 1+(-70707087/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((273342417/625000000 : ℝ)*X 0 0+(849603337/2000000000 : ℝ)*X 0 1+(450268243/1000000000 : ℝ)*X 0 2+(273342417/625000000 : ℝ)*X 1 0+(849603337/2000000000 : ℝ)*X 1 1+(450268243/1000000000 : ℝ)*X 1 2+(273342417/625000000 : ℝ)*X 2 0+(849603337/2000000000 : ℝ)*X 2 1+(450268243/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-549222383/2500000000 : ℝ)*X 0 0+(2632473799/5000000000 : ℝ)*X 0 1+(2696938113/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312293143/10000000000 : ℝ)*X 1 0+(-266671639/1250000000 : ℝ)*X 1 1+(2696938113/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664036643/1250000000 : ℝ)*X 2 0+(215755049/400000000 : ℝ)*X 2 1+(-2133373111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4373488073/10000000000 : ℝ)*X 0 0+(562755411/1250000000 : ℝ)*X 0 1+(531082333/1250000000 : ℝ)*X 0 2+(4373488073/10000000000 : ℝ)*X 1 0+(562755411/1250000000 : ℝ)*X 1 1+(531082333/1250000000 : ℝ)*X 1 2+(4373488073/10000000000 : ℝ)*X 2 0+(562755411/1250000000 : ℝ)*X 2 1+(531082333/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2831032011210668225403569/359765625000000000000000000000 : ℝ) := by norm_num
    linear_combination (654950553/100000000000000 : ℝ)*(base19) + (180208717/50000000000000 : ℝ)*(lower2) + (80301599/100000000000000 : ℝ)*(lower4) + (44042199/12500000000000 : ℝ)*(upper5) + (181937544577127/3125000000000 : ℝ)*(major0) + (181937544577127/3125000000000 : ℝ)*(major1) + (181937544577127/3125000000000 : ℝ)*(major2) + (482328818166767/6250000000000 : ℝ)*(sp0) + (1543451225979023/20000000000000 : ℝ)*(sp1) + (3858627607687289/50000000000000 : ℝ)*(sp2) + (981682768446407/25000000000000 : ℝ)*(sp3) + (1076455651/25000000000000 : ℝ)*(sp5) + (2937646847/50000000000000 : ℝ)*(sp6) + (208523577/2000000000000 : ℝ)*(sp7) + (1963370749982239/50000000000000 : ℝ)*(f.failure) + (482328818166767/6250000000000 : ℝ)*(f.sum) + (37391766887561/6907500000000000000000000000 : ℝ)*base65 + (142532388378677599/8634375000000000000000000000000 : ℝ)*base67 + (100021751810215099/8634375000000000000000000000000 : ℝ)*base69 + (143438915433546349/8634375000000000000000000000000 : ℝ)*base71 + (11565484038899/1726875000000000000000000000 : ℝ)*base73 + (243840879333728651/8634375000000000000000000000000 : ℝ)*base76 + (12190539219578651/8634375000000000000000000000000 : ℝ)*base78 + (55436060485915099/8634375000000000000000000000000 : ℝ)*base79 + (25851047419931/6907500000000000000000000000 : ℝ)*base81 + (21435291/2500000000000000000000 : ℝ)*base90 + (21435291/2500000000000000000000 : ℝ)*base92 + (21435291/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15617023540453172244033/1535000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9388547/500000000000 : ℝ)*(base19) + (255591009/12500000000000 : ℝ)*(base23) + (50767901/25000000000000 : ℝ)*(upper3) + (15035711/20000000000000 : ℝ)*(lower4) + (206629463/100000000000000 : ℝ)*(upper5) + (5851398299586369/100000000000000 : ℝ)*(major0) + (5851398299586369/100000000000000 : ℝ)*(major1) + (5851398299586369/100000000000000 : ℝ)*(major2) + (5120351541/10000000000000 : ℝ)*(sp1) + (5511221883/10000000000000 : ℝ)*(sp2) + (7756227571247781/100000000000000 : ℝ)*(sp4) + (7756174490022971/100000000000000 : ℝ)*(sp5) + (96952130178761/1250000000000 : ℝ)*(sp6) + (1973284344396529/50000000000000 : ℝ)*(sp7) + (1973284344396529/50000000000000 : ℝ)*(f.failure) + (7756227571247781/100000000000000 : ℝ)*(f.sum) + (403570835021/71953125000000000000000000 : ℝ)*base65 + (869510347351812151/92100000000000000000000000000000 : ℝ)*base67 + (1330899959467787849/92100000000000000000000000000000 : ℝ)*base70 + (228273537141312151/92100000000000000000000000000000 : ℝ)*base71 + (12718001229247/2302500000000000000000000000 : ℝ)*base73 + (1341320356087787849/92100000000000000000000000000000 : ℝ)*base76 + (615882741929387849/92100000000000000000000000000000 : ℝ)*base78 + (1095048259734612151/92100000000000000000000000000000 : ℝ)*base79 + (3195632106247/2302500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (16690699/2500000000000000000000 : ℝ)*base89 + (16690699/2500000000000000000000 : ℝ)*base91 + (16690699/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1080_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14023/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (563/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1080_s8_0 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-10984457/50000000 : ℝ)*x 0 + (2697053953/5000000000 : ℝ)*x 1 + (2632356331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10984457/50000000 : ℝ)^8273 ≤ (1334339239811/10000000000000 : ℝ)^6225 := by
    have hnat : (10984457 : ℕ)^8273*10000000000000^6225 ≤ 1334339239811^6225*50000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10984457 50000000 1334339239811 10000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697053953/5000000000 : ℝ)^8273 ≤ (44027321492147/100000000000000 : ℝ)^6225 := by
    have hnat : (2697053953 : ℕ)^8273*100000000000000^6225 ≤ 44027321492147^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697053953 5000000000 44027321492147 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632356331/5000000000 : ℝ)^8273 ≤ (106573215239/250000000000 : ℝ)^6225 := by
    have hnat : (2632356331 : ℕ)^8273*250000000000^6225 ≤ 106573215239^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632356331 5000000000 106573215239 250000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10984457/50000000 : ℝ), (2697053953/5000000000 : ℝ), (2632356331/5000000000 : ℝ)] ![(1334339239811/10000000000000 : ℝ), (44027321492147/100000000000000 : ℝ), (106573215239/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10984457/50000000 : ℝ)|^8273 ≤ (1334339239811/10000000000000 : ℝ)^6225
        have hw : |(-10984457/50000000 : ℝ)|=(10984457/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697053953/5000000000 : ℝ)|^8273 ≤ (44027321492147/100000000000000 : ℝ)^6225
        have hw : |(2697053953/5000000000 : ℝ)|=(2697053953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632356331/5000000000 : ℝ)|^8273 ≤ (106573215239/250000000000 : ℝ)^6225
        have hw : |(2632356331/5000000000 : ℝ)|=(2632356331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s8_1 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344944691/10000000000 : ℝ)*x 0 + (-2262538683/10000000000 : ℝ)*x 1 + (5264712663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344944691/10000000000 : ℝ)^8273 ≤ (1087370720697/2500000000000 : ℝ)^6225 := by
    have hnat : (5344944691 : ℕ)^8273*2500000000000^6225 ≤ 1087370720697^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344944691 10000000000 1087370720697 2500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262538683/10000000000 : ℝ)^8273 ≤ (3468971262763/25000000000000 : ℝ)^6225 := by
    have hnat : (2262538683 : ℕ)^8273*25000000000000^6225 ≤ 3468971262763^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262538683 10000000000 3468971262763 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264712663/10000000000 : ℝ)^8273 ≤ (42629286106361/100000000000000 : ℝ)^6225 := by
    have hnat : (5264712663 : ℕ)^8273*100000000000000^6225 ≤ 42629286106361^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264712663 10000000000 42629286106361 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344944691/10000000000 : ℝ), (-2262538683/10000000000 : ℝ), (5264712663/10000000000 : ℝ)] ![(1087370720697/2500000000000 : ℝ), (3468971262763/25000000000000 : ℝ), (42629286106361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344944691/10000000000 : ℝ)|^8273 ≤ (1087370720697/2500000000000 : ℝ)^6225
        have hw : |(5344944691/10000000000 : ℝ)|=(5344944691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2262538683/10000000000 : ℝ)|^8273 ≤ (3468971262763/25000000000000 : ℝ)^6225
        have hw : |(-2262538683/10000000000 : ℝ)|=(2262538683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264712663/10000000000 : ℝ)|^8273 ≤ (42629286106361/100000000000000 : ℝ)^6225
        have hw : |(5264712663/10000000000 : ℝ)|=(5264712663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s8_2 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672472361/5000000000 : ℝ)*x 0 + (5264712633/10000000000 : ℝ)*x 1 + (-2262538681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672472361/5000000000 : ℝ)^8273 ≤ (43494829163139/100000000000000 : ℝ)^6225 := by
    have hnat : (2672472361 : ℕ)^8273*100000000000000^6225 ≤ 43494829163139^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672472361 5000000000 43494829163139 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264712633/10000000000 : ℝ)^8273 ≤ (5328660722941/12500000000000 : ℝ)^6225 := by
    have hnat : (5264712633 : ℕ)^8273*12500000000000^6225 ≤ 5328660722941^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264712633 10000000000 5328660722941 12500000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262538681/10000000000 : ℝ)^8273 ≤ (13875885034751/100000000000000 : ℝ)^6225 := by
    have hnat : (2262538681 : ℕ)^8273*100000000000000^6225 ≤ 13875885034751^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262538681 10000000000 13875885034751 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672472361/5000000000 : ℝ), (5264712633/10000000000 : ℝ), (-2262538681/10000000000 : ℝ)] ![(43494829163139/100000000000000 : ℝ), (5328660722941/12500000000000 : ℝ), (13875885034751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672472361/5000000000 : ℝ)|^8273 ≤ (43494829163139/100000000000000 : ℝ)^6225
        have hw : |(2672472361/5000000000 : ℝ)|=(2672472361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264712633/10000000000 : ℝ)|^8273 ≤ (5328660722941/12500000000000 : ℝ)^6225
        have hw : |(5264712633/10000000000 : ℝ)|=(5264712633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2262538681/10000000000 : ℝ)|^8273 ≤ (13875885034751/100000000000000 : ℝ)^6225
        have hw : |(-2262538681/10000000000 : ℝ)|=(2262538681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s8_3 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4373482853/10000000000 : ℝ)*x 0 + (265512399/625000000 : ℝ)*x 1 + (2251250017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4373482853/10000000000 : ℝ)^8273 ≤ (33316632200463/100000000000000 : ℝ)^6225 := by
    have hnat : (4373482853 : ℕ)^8273*100000000000000^6225 ≤ 33316632200463^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4373482853 10000000000 33316632200463 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265512399/625000000 : ℝ)^8273 ≤ (16027126419839/50000000000000 : ℝ)^6225 := by
    have hnat : (265512399 : ℕ)^8273*50000000000000^6225 ≤ 16027126419839^6225*625000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265512399 625000000 16027126419839 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251250017/5000000000 : ℝ)^8273 ≤ (17314557473741/50000000000000 : ℝ)^6225 := by
    have hnat : (2251250017 : ℕ)^8273*50000000000000^6225 ≤ 17314557473741^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251250017 5000000000 17314557473741 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4373482853/10000000000 : ℝ), (265512399/625000000 : ℝ), (2251250017/5000000000 : ℝ)] ![(33316632200463/100000000000000 : ℝ), (16027126419839/50000000000000 : ℝ), (17314557473741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4373482853/10000000000 : ℝ)|^8273 ≤ (33316632200463/100000000000000 : ℝ)^6225
        have hw : |(4373482853/10000000000 : ℝ)|=(4373482853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(265512399/625000000 : ℝ)|^8273 ≤ (16027126419839/50000000000000 : ℝ)^6225
        have hw : |(265512399/625000000 : ℝ)|=(265512399/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251250017/5000000000 : ℝ)|^8273 ≤ (17314557473741/50000000000000 : ℝ)^6225
        have hw : |(2251250017/5000000000 : ℝ)|=(2251250017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s8_4 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196896417/10000000000 : ℝ)*x 0 + (2632518443/5000000000 : ℝ)*x 1 + (2696891261/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196896417/10000000000 : ℝ)^8273 ≤ (13343432895367/100000000000000 : ℝ)^6225 := by
    have hnat : (2196896417 : ℕ)^8273*100000000000000^6225 ≤ 13343432895367^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196896417 10000000000 13343432895367 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632518443/5000000000 : ℝ)^8273 ≤ (42632775140947/100000000000000 : ℝ)^6225 := by
    have hnat : (2632518443 : ℕ)^8273*100000000000000^6225 ≤ 42632775140947^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632518443 5000000000 42632775140947 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696891261/5000000000 : ℝ)^8273 ≤ (44023791951501/100000000000000 : ℝ)^6225 := by
    have hnat : (2696891261 : ℕ)^8273*100000000000000^6225 ≤ 44023791951501^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696891261 5000000000 44023791951501 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196896417/10000000000 : ℝ), (2632518443/5000000000 : ℝ), (2696891261/5000000000 : ℝ)] ![(13343432895367/100000000000000 : ℝ), (42632775140947/100000000000000 : ℝ), (44023791951501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196896417/10000000000 : ℝ)|^8273 ≤ (13343432895367/100000000000000 : ℝ)^6225
        have hw : |(-2196896417/10000000000 : ℝ)|=(2196896417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632518443/5000000000 : ℝ)|^8273 ≤ (42632775140947/100000000000000 : ℝ)^6225
        have hw : |(2632518443/5000000000 : ℝ)|=(2632518443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696891261/5000000000 : ℝ)|^8273 ≤ (44023791951501/100000000000000 : ℝ)^6225
        have hw : |(2696891261/5000000000 : ℝ)|=(2696891261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s8_5 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312316443/10000000000 : ℝ)*x 0 + (-1066734399/5000000000 : ℝ)*x 1 + (5393782521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312316443/10000000000 : ℝ)^8273 ≤ (10785579003637/25000000000000 : ℝ)^6225 := by
    have hnat : (5312316443 : ℕ)^8273*25000000000000^6225 ≤ 10785579003637^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312316443 10000000000 10785579003637 25000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1066734399/5000000000 : ℝ)^8273 ≤ (2566778406531/20000000000000 : ℝ)^6225 := by
    have hnat : (1066734399 : ℕ)^8273*20000000000000^6225 ≤ 2566778406531^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066734399 5000000000 2566778406531 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393782521/10000000000 : ℝ)^8273 ≤ (22011895970327/50000000000000 : ℝ)^6225 := by
    have hnat : (5393782521 : ℕ)^8273*50000000000000^6225 ≤ 22011895970327^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393782521 10000000000 22011895970327 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312316443/10000000000 : ℝ), (-1066734399/5000000000 : ℝ), (5393782521/10000000000 : ℝ)] ![(10785579003637/25000000000000 : ℝ), (2566778406531/20000000000000 : ℝ), (22011895970327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312316443/10000000000 : ℝ)|^8273 ≤ (10785579003637/25000000000000 : ℝ)^6225
        have hw : |(5312316443/10000000000 : ℝ)|=(5312316443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1066734399/5000000000 : ℝ)|^8273 ≤ (2566778406531/20000000000000 : ℝ)^6225
        have hw : |(-1066734399/5000000000 : ℝ)|=(1066734399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393782521/10000000000 : ℝ)|^8273 ≤ (22011895970327/50000000000000 : ℝ)^6225
        have hw : |(5393782521/10000000000 : ℝ)|=(5393782521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s8_6 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656158221/5000000000 : ℝ)*x 0 + (2696891261/5000000000 : ℝ)*x 1 + (-1066734399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656158221/5000000000 : ℝ)^8273 ≤ (8628463200751/20000000000000 : ℝ)^6225 := by
    have hnat : (2656158221 : ℕ)^8273*20000000000000^6225 ≤ 8628463200751^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656158221 5000000000 8628463200751 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696891261/5000000000 : ℝ)^8273 ≤ (44023791951501/100000000000000 : ℝ)^6225 := by
    have hnat : (2696891261 : ℕ)^8273*100000000000000^6225 ≤ 44023791951501^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696891261 5000000000 44023791951501 100000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1066734399/5000000000 : ℝ)^8273 ≤ (2566778406531/20000000000000 : ℝ)^6225 := by
    have hnat : (1066734399 : ℕ)^8273*20000000000000^6225 ≤ 2566778406531^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1066734399 5000000000 2566778406531 20000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656158221/5000000000 : ℝ), (2696891261/5000000000 : ℝ), (-1066734399/5000000000 : ℝ)] ![(8628463200751/20000000000000 : ℝ), (44023791951501/100000000000000 : ℝ), (2566778406531/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656158221/5000000000 : ℝ)|^8273 ≤ (8628463200751/20000000000000 : ℝ)^6225
        have hw : |(2656158221/5000000000 : ℝ)|=(2656158221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696891261/5000000000 : ℝ)|^8273 ≤ (44023791951501/100000000000000 : ℝ)^6225
        have hw : |(2696891261/5000000000 : ℝ)|=(2696891261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1066734399/5000000000 : ℝ)|^8273 ≤ (2566778406531/20000000000000 : ℝ)^6225
        have hw : |(-1066734399/5000000000 : ℝ)|=(1066734399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1080_s8_7 (p : ℝ) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546686593/1250000000 : ℝ)*x 0 + (4501862847/10000000000 : ℝ)*x 1 + (2124418929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546686593/1250000000 : ℝ)^8273 ≤ (16658366169091/50000000000000 : ℝ)^6225 := by
    have hnat : (546686593 : ℕ)^8273*50000000000000^6225 ≤ 16658366169091^6225*1250000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546686593 1250000000 16658366169091 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501862847/10000000000 : ℝ)^8273 ≤ (540978158463/1562500000000 : ℝ)^6225 := by
    have hnat : (4501862847 : ℕ)^8273*1562500000000^6225 ≤ 540978158463^6225*10000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501862847 10000000000 540978158463 1562500000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124418929/5000000000 : ℝ)^8273 ≤ (16030332749603/50000000000000 : ℝ)^6225 := by
    have hnat : (2124418929 : ℕ)^8273*50000000000000^6225 ≤ 16030332749603^6225*5000000000^8273 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124418929 5000000000 16030332749603 50000000000000 8273 6225 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8273/2048 : ℝ)) 8273 6225 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546686593/1250000000 : ℝ), (4501862847/10000000000 : ℝ), (2124418929/5000000000 : ℝ)] ![(16658366169091/50000000000000 : ℝ), (540978158463/1562500000000 : ℝ), (16030332749603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546686593/1250000000 : ℝ)|^8273 ≤ (16658366169091/50000000000000 : ℝ)^6225
        have hw : |(546686593/1250000000 : ℝ)|=(546686593/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501862847/10000000000 : ℝ)|^8273 ≤ (540978158463/1562500000000 : ℝ)^6225
        have hw : |(4501862847/10000000000 : ℝ)|=(4501862847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124418929/5000000000 : ℝ)|^8273 ≤ (16030332749603/50000000000000 : ℝ)^6225
        have hw : |(2124418929/5000000000 : ℝ)|=(2124418929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1080_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11271/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3503/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11269/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11269/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11269/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11269/100000 : ℝ) ^ (517/128 : ℝ) ≤ (925519994567821/6250000000000000000 : ℝ) := by
    have hpowers : (11269/100000 : ℝ)^517 ≤ (925519994567821/6250000000000000000 : ℝ)^128 := by
      have hnat : (11269 : ℕ)^517*6250000000000000000^128 ≤ 925519994567821^128*100000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11269 100000 925519994567821 6250000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11269/100000 : ℝ)) (X := (925519994567821/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7007/50000 : ℝ) ^ (517/128 : ℝ) ≤ (285759726908623/800000000000000000 : ℝ) := by
    have hpowers : (7007/50000 : ℝ)^517 ≤ (285759726908623/800000000000000000 : ℝ)^128 := by
      have hnat : (7007 : ℕ)^517*800000000000000000^128 ≤ 285759726908623^128*50000^517 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7007 50000 285759726908623 800000000000000000 517 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7007/50000 : ℝ)) (X := (285759726908623/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125925519994567821/3125000000000000000 : ℝ) ≤ (10000733173613879/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (3125925519994567821/3125000000000000000 : ℝ)^128 ≤ (10000733173613879/10000000000000000 : ℝ)^517 := by
      have hnat : (3125925519994567821 : ℕ)^128*10000000000000000^517 ≤ 10000733173613879^517*3125000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125925519994567821 3125000000000000000 10000733173613879 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000733173613879/10000000000000000 : ℝ)) (X := (3125925519994567821/3125000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050528285776663011/100000000000000000000 : ℝ) ≤ (10001250752707899/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (100050528285776663011/100000000000000000000 : ℝ)^128 ≤ (10001250752707899/10000000000000000 : ℝ)^517 := by
      have hnat : (100050528285776663011 : ℕ)^128*10000000000000000^517 ≤ 10001250752707899^517*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050528285776663011 100000000000000000000 10001250752707899 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001250752707899/10000000000000000 : ℝ)) (X := (100050528285776663011/100000000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (400285759726908623/400000000000000000 : ℝ) ≤ (10001768331801919/10000000000000000 : ℝ) ^ (517/128 : ℝ) := by
    have hpowers : (400285759726908623/400000000000000000 : ℝ)^128 ≤ (10001768331801919/10000000000000000 : ℝ)^517 := by
      have hnat : (400285759726908623 : ℕ)^128*10000000000000000^517 ≤ 10001768331801919^517*400000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400285759726908623 400000000000000000 10001768331801919 10000000000000000 128 517 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001768331801919/10000000000000000 : ℝ)) (X := (400285759726908623/400000000000000000 : ℝ)) (by norm_num) 517 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(925519994567821/6250000000000000000 : ℝ) ≤ ((5488069472789815019/5490000000000000000 : ℝ)+2*(25878954701/13725000000000 : ℝ)*(11269/100000 : ℝ))^(517/128 : ℝ) := by
    rw [show (5488069472789815019/5490000000000000000 : ℝ)+2*(25878954701/13725000000000 : ℝ)*(11269/100000 : ℝ)=(10000733173613879/10000000000000000 : ℝ) by norm_num, show 1+2*(925519994567821/6250000000000000000 : ℝ)=(3125925519994567821/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(285759726908623/800000000000000000 : ℝ)+(925519994567821/6250000000000000000 : ℝ) ≤ ((5488069472789815019/5490000000000000000 : ℝ)+(25878954701/13725000000000 : ℝ)*((7007/50000 : ℝ)+(11269/100000 : ℝ)))^(517/128 : ℝ) := by
    rw [show (5488069472789815019/5490000000000000000 : ℝ)+(25878954701/13725000000000 : ℝ)*((7007/50000 : ℝ)+(11269/100000 : ℝ))=(10001250752707899/10000000000000000 : ℝ) by norm_num, show 1+(285759726908623/800000000000000000 : ℝ)+(925519994567821/6250000000000000000 : ℝ)=(100050528285776663011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(285759726908623/800000000000000000 : ℝ) ≤ ((5488069472789815019/5490000000000000000 : ℝ)+2*(25878954701/13725000000000 : ℝ)*(7007/50000 : ℝ))^(517/128 : ℝ) := by
    rw [show (5488069472789815019/5490000000000000000 : ℝ)+2*(25878954701/13725000000000 : ℝ)*(7007/50000 : ℝ)=(10001768331801919/10000000000000000 : ℝ) by norm_num, show 1+2*(285759726908623/800000000000000000 : ℝ)=(400285759726908623/400000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5488069472789815019/5490000000000000000 : ℝ)*(X 1 0+X 2 0)+(25878954701/13725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (5488069472789815019/5490000000000000000 : ℝ)) (alpha := (25878954701/13725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5488069472789815019/5490000000000000000 : ℝ)*(X 0 1+X 2 1)+(25878954701/13725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (5488069472789815019/5490000000000000000 : ℝ)) (alpha := (25878954701/13725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5488069472789815019/5490000000000000000 : ℝ)*(X 0 2+X 1 2)+(25878954701/13725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (517/128 : ℝ)) (lo := (11269/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (5488069472789815019/5490000000000000000 : ℝ)) (alpha := (25878954701/13725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-10984457/50000000 : ℝ)*X 0 0+(2697053953/5000000000 : ℝ)*X 0 1+(2632356331/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344944691/10000000000 : ℝ)*X 1 0+(-2262538683/10000000000 : ℝ)*X 1 1+(5264712663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672472361/5000000000 : ℝ)*X 2 0+(5264712633/10000000000 : ℝ)*X 2 1+(-2262538681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4373482853/10000000000 : ℝ)*X 0 0+(265512399/625000000 : ℝ)*X 0 1+(2251250017/5000000000 : ℝ)*X 0 2+(4373482853/10000000000 : ℝ)*X 1 0+(265512399/625000000 : ℝ)*X 1 1+(2251250017/5000000000 : ℝ)*X 1 2+(4373482853/10000000000 : ℝ)*X 2 0+(265512399/625000000 : ℝ)*X 2 1+(2251250017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2196896417/10000000000 : ℝ)*X 0 0+(2632518443/5000000000 : ℝ)*X 0 1+(2696891261/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312316443/10000000000 : ℝ)*X 1 0+(-1066734399/5000000000 : ℝ)*X 1 1+(5393782521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656158221/5000000000 : ℝ)*X 2 0+(2696891261/5000000000 : ℝ)*X 2 1+(-1066734399/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((546686593/1250000000 : ℝ)*X 0 0+(4501862847/10000000000 : ℝ)*X 0 1+(2124418929/5000000000 : ℝ)*X 0 2+(546686593/1250000000 : ℝ)*X 1 0+(4501862847/10000000000 : ℝ)*X 1 1+(2124418929/5000000000 : ℝ)*X 1 2+(546686593/1250000000 : ℝ)*X 2 0+(4501862847/10000000000 : ℝ)*X 2 1+(2124418929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1080_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (175463970882678361489/38125000000000000000000000 : ℝ) := by norm_num
    linear_combination (217235727/25000000000000 : ℝ)*(base19) + (872643521/100000000000000 : ℝ)*(base23) + (21979791/100000000000000 : ℝ)*(lower2) + (104741037/100000000000000 : ℝ)*(upper3) + (17093457/20000000000000 : ℝ)*(upper5) + (5830334278677197/100000000000000 : ℝ)*(major0) + (5830334278677197/100000000000000 : ℝ)*(major1) + (5830334278677197/100000000000000 : ℝ)*(major2) + (7728282854813959/100000000000000 : ℝ)*(sp0) + (3864152905136829/50000000000000 : ℝ)*(sp1) + (1932076451643261/25000000000000 : ℝ)*(sp2) + (1966174661662193/50000000000000 : ℝ)*(sp3) + (23824402607/100000000000000 : ℝ)*(sp4) + (2480280461/20000000000000 : ℝ)*(sp7) + (983090431181673/25000000000000 : ℝ)*(f.failure) + (3864153339608283/50000000000000 : ℝ)*(f.sum) + (11061634932433/2745000000000000000000000000 : ℝ)*base65 + (5568798084847221743/549000000000000000000000000000000 : ℝ)*base67 + (5285809936891778257/549000000000000000000000000000000 : ℝ)*base70 + (10332987816061778257/549000000000000000000000000000000 : ℝ)*base72 + (22611426424363/2745000000000000000000000000 : ℝ)*base73 + (7649482362550221743/549000000000000000000000000000000 : ℝ)*base75 + (6408200041471778257/549000000000000000000000000000000 : ℝ)*base78 + (16541417770243221743/549000000000000000000000000000000 : ℝ)*base79 + (1730007579569/1372500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (14138963/1250000000000000000000 : ℝ)*base89 + (14138963/1250000000000000000000 : ℝ)*base91 + (14138963/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1837623210671766502997/183000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1857833703/100000000000000 : ℝ)*(base19) + (504779841/25000000000000 : ℝ)*(base23) + (327085121/50000000000000 : ℝ)*(lower1) + (200811631/100000000000000 : ℝ)*(upper3) + (74021537/100000000000000 : ℝ)*(lower4) + (20401551/10000000000000 : ℝ)*(upper5) + (1171935357151013/20000000000000 : ℝ)*(major0) + (1171935357151013/20000000000000 : ℝ)*(major1) + (1171935357151013/20000000000000 : ℝ)*(major2) + (3811184629/100000000000000 : ℝ)*(sp2) + (7767200991273963/100000000000000 : ℝ)*(sp4) + (7767199133440259/100000000000000 : ℝ)*(sp5) + (7767195160969969/100000000000000 : ℝ)*(sp6) + (1976076122757121/50000000000000 : ℝ)*(sp7) + (1976076122757121/50000000000000 : ℝ)*(f.failure) + (7767200991273963/100000000000000 : ℝ)*(f.sum) + (148165405579/549000000000000000000000000 : ℝ)*base65 + (531571592082064247/109800000000000000000000000000000 : ℝ)*base67 + (1140963554208064247/109800000000000000000000000000000 : ℝ)*base69 + (10350198041370664247/109800000000000000000000000000000 : ℝ)*base71 + (29857930241/34312500000000000000000000 : ℝ)*base74 + (14170518885971335753/109800000000000000000000000000000 : ℝ)*base76 + (770799399579535753/109800000000000000000000000000000 : ℝ)*base78 + (1557307611036535753/109800000000000000000000000000000 : ℝ)*base80 + (2393277546727/549000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4427451/2500000000000000000000 : ℝ)*base89 + (4427451/2500000000000000000000 : ℝ)*base91 + (4427451/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1080_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11269/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1080_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1080_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1080_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1080_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1080_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (517/128 : ℝ) ≤ p) (hpb : p ≤ (8273/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74132731/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (879/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11221/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11271/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3503/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1080_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
