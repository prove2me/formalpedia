-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1343_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:47.795315+00:00
-- url     : https://prove2.me/submissions/6a1dee65-792f-4a08-93a0-598bf4b4dab3

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
theorem support_rectangle_w1343_s0_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-226069403/1250000000 : ℝ)*x 0 + (599648489/1000000000 : ℝ)*x 1 + (2405573817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (226069403/1250000000 : ℝ)^4303 ≤ (2120477472893/20000000000000 : ℝ)^3279 := by
    have hnat : (226069403 : ℕ)^4303*20000000000000^3279 ≤ 2120477472893^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226069403 1250000000 2120477472893 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (599648489/1000000000 : ℝ)^4303 ≤ (12778387464203/25000000000000 : ℝ)^3279 := by
    have hnat : (599648489 : ℕ)^4303*25000000000000^3279 ≤ 12778387464203^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      599648489 1000000000 12778387464203 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405573817/5000000000 : ℝ)^4303 ≤ (382840627701/1000000000000 : ℝ)^3279 := by
    have hnat : (2405573817 : ℕ)^4303*1000000000000^3279 ≤ 382840627701^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405573817 5000000000 382840627701 1000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-226069403/1250000000 : ℝ), (599648489/1000000000 : ℝ), (2405573817/5000000000 : ℝ)] ![(2120477472893/20000000000000 : ℝ), (12778387464203/25000000000000 : ℝ), (382840627701/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-226069403/1250000000 : ℝ)|^4303 ≤ (2120477472893/20000000000000 : ℝ)^3279
        have hw : |(-226069403/1250000000 : ℝ)|=(226069403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(599648489/1000000000 : ℝ)|^4303 ≤ (12778387464203/25000000000000 : ℝ)^3279
        have hw : |(599648489/1000000000 : ℝ)|=(599648489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405573817/5000000000 : ℝ)|^4303 ≤ (382840627701/1000000000000 : ℝ)^3279
        have hw : |(2405573817/5000000000 : ℝ)|=(2405573817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s0_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5501700611/10000000000 : ℝ)*x 0 + (-2482246523/10000000000 : ℝ)*x 1 + (2405574023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5501700611/10000000000 : ℝ)^4303 ≤ (9130333822371/20000000000000 : ℝ)^3279 := by
    have hnat : (5501700611 : ℕ)^4303*20000000000000^3279 ≤ 9130333822371^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501700611 10000000000 9130333822371 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2482246523/10000000000 : ℝ)^4303 ≤ (642570551739/4000000000000 : ℝ)^3279 := by
    have hnat : (2482246523 : ℕ)^4303*4000000000000^3279 ≤ 642570551739^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482246523 10000000000 642570551739 4000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2405574023/5000000000 : ℝ)^4303 ≤ (38284067072359/100000000000000 : ℝ)^3279 := by
    have hnat : (2405574023 : ℕ)^4303*100000000000000^3279 ≤ 38284067072359^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405574023 5000000000 38284067072359 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5501700611/10000000000 : ℝ), (-2482246523/10000000000 : ℝ), (2405574023/5000000000 : ℝ)] ![(9130333822371/20000000000000 : ℝ), (642570551739/4000000000000 : ℝ), (38284067072359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5501700611/10000000000 : ℝ)|^4303 ≤ (9130333822371/20000000000000 : ℝ)^3279
        have hw : |(5501700611/10000000000 : ℝ)|=(5501700611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2482246523/10000000000 : ℝ)|^4303 ≤ (642570551739/4000000000000 : ℝ)^3279
        have hw : |(-2482246523/10000000000 : ℝ)|=(2482246523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2405574023/5000000000 : ℝ)|^4303 ≤ (38284067072359/100000000000000 : ℝ)^3279
        have hw : |(2405574023/5000000000 : ℝ)|=(2405574023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s0_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2750850161/5000000000 : ℝ)*x 0 + (601393479/1250000000 : ℝ)*x 1 + (-1241123579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2750850161/5000000000 : ℝ)^4303 ≤ (22825832982461/50000000000000 : ℝ)^3279 := by
    have hnat : (2750850161 : ℕ)^4303*50000000000000^3279 ≤ 22825832982461^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750850161 5000000000 22825832982461 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601393479/1250000000 : ℝ)^4303 ≤ (3828406483769/10000000000000 : ℝ)^3279 := by
    have hnat : (601393479 : ℕ)^4303*10000000000000^3279 ≤ 3828406483769^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601393479 1250000000 3828406483769 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1241123579/5000000000 : ℝ)^4303 ≤ (803213459317/5000000000000 : ℝ)^3279 := by
    have hnat : (1241123579 : ℕ)^4303*5000000000000^3279 ≤ 803213459317^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1241123579 5000000000 803213459317 5000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2750850161/5000000000 : ℝ), (601393479/1250000000 : ℝ), (-1241123579/5000000000 : ℝ)] ![(22825832982461/50000000000000 : ℝ), (3828406483769/10000000000000 : ℝ), (803213459317/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2750850161/5000000000 : ℝ)|^4303 ≤ (22825832982461/50000000000000 : ℝ)^3279
        have hw : |(2750850161/5000000000 : ℝ)|=(2750850161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601393479/1250000000 : ℝ)|^4303 ≤ (3828406483769/10000000000000 : ℝ)^3279
        have hw : |(601393479/1250000000 : ℝ)|=(601393479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1241123579/5000000000 : ℝ)|^4303 ≤ (803213459317/5000000000000 : ℝ)^3279
        have hw : |(-1241123579/5000000000 : ℝ)|=(1241123579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s0_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2089298523/5000000000 : ℝ)*x 0 + (3106516061/10000000000 : ℝ)*x 1 + (5590223977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2089298523/5000000000 : ℝ)^4303 ≤ (15909333428679/50000000000000 : ℝ)^3279 := by
    have hnat : (2089298523 : ℕ)^4303*50000000000000^3279 ≤ 15909333428679^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089298523 5000000000 15909333428679 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3106516061/10000000000 : ℝ)^4303 ≤ (431266330703/2000000000000 : ℝ)^3279 := by
    have hnat : (3106516061 : ℕ)^4303*2000000000000^3279 ≤ 431266330703^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106516061 10000000000 431266330703 2000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5590223977/10000000000 : ℝ)^4303 ≤ (46618016602613/100000000000000 : ℝ)^3279 := by
    have hnat : (5590223977 : ℕ)^4303*100000000000000^3279 ≤ 46618016602613^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5590223977 10000000000 46618016602613 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2089298523/5000000000 : ℝ), (3106516061/10000000000 : ℝ), (5590223977/10000000000 : ℝ)] ![(15909333428679/50000000000000 : ℝ), (431266330703/2000000000000 : ℝ), (46618016602613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2089298523/5000000000 : ℝ)|^4303 ≤ (15909333428679/50000000000000 : ℝ)^3279
        have hw : |(2089298523/5000000000 : ℝ)|=(2089298523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3106516061/10000000000 : ℝ)|^4303 ≤ (431266330703/2000000000000 : ℝ)^3279
        have hw : |(3106516061/10000000000 : ℝ)|=(3106516061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5590223977/10000000000 : ℝ)|^4303 ≤ (46618016602613/100000000000000 : ℝ)^3279
        have hw : |(5590223977/10000000000 : ℝ)|=(5590223977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s0_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1813006571/10000000000 : ℝ)*x 0 + (4841653661/10000000000 : ℝ)*x 1 + (5964889699/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1813006571/10000000000 : ℝ)^4303 ≤ (1063664521049/10000000000000 : ℝ)^3279 := by
    have hnat : (1813006571 : ℕ)^4303*10000000000000^3279 ≤ 1063664521049^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813006571 10000000000 1063664521049 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4841653661/10000000000 : ℝ)^4303 ≤ (19301466531863/50000000000000 : ℝ)^3279 := by
    have hnat : (4841653661 : ℕ)^4303*50000000000000^3279 ≤ 19301466531863^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4841653661 10000000000 19301466531863 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5964889699/10000000000 : ℝ)^4303 ≤ (10152084342619/20000000000000 : ℝ)^3279 := by
    have hnat : (5964889699 : ℕ)^4303*20000000000000^3279 ≤ 10152084342619^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964889699 10000000000 10152084342619 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1813006571/10000000000 : ℝ), (4841653661/10000000000 : ℝ), (5964889699/10000000000 : ℝ)] ![(1063664521049/10000000000000 : ℝ), (19301466531863/50000000000000 : ℝ), (10152084342619/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1813006571/10000000000 : ℝ)|^4303 ≤ (1063664521049/10000000000000 : ℝ)^3279
        have hw : |(-1813006571/10000000000 : ℝ)|=(1813006571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4841653661/10000000000 : ℝ)|^4303 ≤ (19301466531863/50000000000000 : ℝ)^3279
        have hw : |(4841653661/10000000000 : ℝ)|=(4841653661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5964889699/10000000000 : ℝ)|^4303 ≤ (10152084342619/20000000000000 : ℝ)^3279
        have hw : |(5964889699/10000000000 : ℝ)|=(5964889699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s0_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1294662777/2500000000 : ℝ)*x 0 + (-1328505851/10000000000 : ℝ)*x 1 + (2982444731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1294662777/2500000000 : ℝ)^4303 ≤ (21083333617311/50000000000000 : ℝ)^3279 := by
    have hnat : (1294662777 : ℕ)^4303*50000000000000^3279 ≤ 21083333617311^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294662777 2500000000 21083333617311 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1328505851/10000000000 : ℝ)^4303 ≤ (353645684579/5000000000000 : ℝ)^3279 := by
    have hnat : (1328505851 : ℕ)^4303*5000000000000^3279 ≤ 353645684579^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328505851 10000000000 353645684579 5000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2982444731/5000000000 : ℝ)^4303 ≤ (50760419066417/100000000000000 : ℝ)^3279 := by
    have hnat : (2982444731 : ℕ)^4303*100000000000000^3279 ≤ 50760419066417^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982444731 5000000000 50760419066417 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1294662777/2500000000 : ℝ), (-1328505851/10000000000 : ℝ), (2982444731/5000000000 : ℝ)] ![(21083333617311/50000000000000 : ℝ), (353645684579/5000000000000 : ℝ), (50760419066417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1294662777/2500000000 : ℝ)|^4303 ≤ (21083333617311/50000000000000 : ℝ)^3279
        have hw : |(1294662777/2500000000 : ℝ)|=(1294662777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1328505851/10000000000 : ℝ)|^4303 ≤ (353645684579/5000000000000 : ℝ)^3279
        have hw : |(-1328505851/10000000000 : ℝ)|=(1328505851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2982444731/5000000000 : ℝ)|^4303 ≤ (50760419066417/100000000000000 : ℝ)^3279
        have hw : |(2982444731/5000000000 : ℝ)|=(2982444731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s0_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5178651093/10000000000 : ℝ)*x 0 + (5964889703/10000000000 : ℝ)*x 1 + (-664252743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178651093/10000000000 : ℝ)^4303 ≤ (5270833384293/12500000000000 : ℝ)^3279 := by
    have hnat : (5178651093 : ℕ)^4303*12500000000000^3279 ≤ 5270833384293^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178651093 10000000000 5270833384293 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5964889703/10000000000 : ℝ)^4303 ≤ (10152084351553/20000000000000 : ℝ)^3279 := by
    have hnat : (5964889703 : ℕ)^4303*20000000000000^3279 ≤ 10152084351553^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964889703 10000000000 10152084351553 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (664252743/5000000000 : ℝ)^4303 ≤ (3536455570739/50000000000000 : ℝ)^3279 := by
    have hnat : (664252743 : ℕ)^4303*50000000000000^3279 ≤ 3536455570739^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664252743 5000000000 3536455570739 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178651093/10000000000 : ℝ), (5964889703/10000000000 : ℝ), (-664252743/5000000000 : ℝ)] ![(5270833384293/12500000000000 : ℝ), (10152084351553/20000000000000 : ℝ), (3536455570739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178651093/10000000000 : ℝ)|^4303 ≤ (5270833384293/12500000000000 : ℝ)^3279
        have hw : |(5178651093/10000000000 : ℝ)|=(5178651093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5964889703/10000000000 : ℝ)|^4303 ≤ (10152084351553/20000000000000 : ℝ)^3279
        have hw : |(5964889703/10000000000 : ℝ)|=(5964889703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-664252743/5000000000 : ℝ)|^4303 ≤ (3536455570739/50000000000000 : ℝ)^3279
        have hw : |(-664252743/5000000000 : ℝ)|=(664252743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s0_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4187922297/10000000000 : ℝ)*x 0 + (552630377/1000000000 : ℝ)*x 1 + (49573731/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4187922297/10000000000 : ℝ)^4303 ≤ (15955941720141/50000000000000 : ℝ)^3279 := by
    have hnat : (4187922297 : ℕ)^4303*50000000000000^3279 ≤ 15955941720141^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187922297 10000000000 15955941720141 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552630377/1000000000 : ℝ)^4303 ≤ (11479940199827/25000000000000 : ℝ)^3279 := by
    have hnat : (552630377 : ℕ)^4303*25000000000000^3279 ≤ 11479940199827^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552630377 1000000000 11479940199827 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49573731/156250000 : ℝ)^4303 ≤ (11084177873163/50000000000000 : ℝ)^3279 := by
    have hnat : (49573731 : ℕ)^4303*50000000000000^3279 ≤ 11084177873163^3279*156250000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49573731 156250000 11084177873163 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4187922297/10000000000 : ℝ), (552630377/1000000000 : ℝ), (49573731/156250000 : ℝ)] ![(15955941720141/50000000000000 : ℝ), (11479940199827/25000000000000 : ℝ), (11084177873163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4187922297/10000000000 : ℝ)|^4303 ≤ (15955941720141/50000000000000 : ℝ)^3279
        have hw : |(4187922297/10000000000 : ℝ)|=(4187922297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552630377/1000000000 : ℝ)|^4303 ≤ (11479940199827/25000000000000 : ℝ)^3279
        have hw : |(552630377/1000000000 : ℝ)|=(552630377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(49573731/156250000 : ℝ)|^4303 ≤ (11084177873163/50000000000000 : ℝ)^3279
        have hw : |(49573731/156250000 : ℝ)|=(49573731/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (711/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1679/6250 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (2151/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2151 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2151*1^512 ≤ 0^512*1^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2151/512 : ℝ) ≤ (425809771372169547/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2151 ≤ (425809771372169547/20000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2151*20000000000000000000^512 ≤ 425809771372169547^512*5^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 425809771372169547 20000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (425809771372169547/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2151 := by
      have hnat : (1 : ℕ)^512*1^2151 ≤ 1^2151*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20425809771372169547/20000000000000000000 : ℝ) ≤ (628141968834049/625000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (20425809771372169547/20000000000000000000 : ℝ)^512 ≤ (628141968834049/625000000000000 : ℝ)^2151 := by
      have hnat : (20425809771372169547 : ℕ)^512*625000000000000^2151 ≤ 628141968834049^2151*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20425809771372169547 20000000000000000000 628141968834049 625000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628141968834049/625000000000000 : ℝ)) (X := (20425809771372169547/20000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10425809771372169547/10000000000000000000 : ℝ) ≤ (315641968834049/312500000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (10425809771372169547/10000000000000000000 : ℝ)^512 ≤ (315641968834049/312500000000000 : ℝ)^2151 := by
      have hnat : (10425809771372169547 : ℕ)^512*312500000000000^2151 ≤ 315641968834049^2151*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10425809771372169547 10000000000000000000 315641968834049 312500000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (315641968834049/312500000000000 : ℝ)) (X := (10425809771372169547/10000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3141968834049/250000000000000 : ℝ)*(0 : ℝ))^(2151/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(3141968834049/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(425809771372169547/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3141968834049/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (1 : ℝ)+(3141968834049/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(628141968834049/625000000000000 : ℝ) by norm_num, show 1+(425809771372169547/20000000000000000000 : ℝ)+(0 : ℝ)=(20425809771372169547/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(425809771372169547/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3141968834049/250000000000000 : ℝ)*(2/5 : ℝ))^(2151/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(3141968834049/250000000000000 : ℝ)*(2/5 : ℝ)=(315641968834049/312500000000000 : ℝ) by norm_num, show 1+2*(425809771372169547/20000000000000000000 : ℝ)=(10425809771372169547/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3141968834049/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3141968834049/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3141968834049/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3141968834049/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3141968834049/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3141968834049/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-226069403/1250000000 : ℝ)*X 0 0+(599648489/1000000000 : ℝ)*X 0 1+(2405573817/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5501700611/10000000000 : ℝ)*X 1 0+(-2482246523/10000000000 : ℝ)*X 1 1+(2405574023/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2750850161/5000000000 : ℝ)*X 2 0+(601393479/1250000000 : ℝ)*X 2 1+(-1241123579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2089298523/5000000000 : ℝ)*X 0 0+(3106516061/10000000000 : ℝ)*X 0 1+(5590223977/10000000000 : ℝ)*X 0 2+(2089298523/5000000000 : ℝ)*X 1 0+(3106516061/10000000000 : ℝ)*X 1 1+(5590223977/10000000000 : ℝ)*X 1 2+(2089298523/5000000000 : ℝ)*X 2 0+(3106516061/10000000000 : ℝ)*X 2 1+(5590223977/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1813006571/10000000000 : ℝ)*X 0 0+(4841653661/10000000000 : ℝ)*X 0 1+(5964889699/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1294662777/2500000000 : ℝ)*X 1 0+(-1328505851/10000000000 : ℝ)*X 1 1+(2982444731/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5178651093/10000000000 : ℝ)*X 2 0+(5964889703/10000000000 : ℝ)*X 2 1+(-664252743/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4187922297/10000000000 : ℝ)*X 0 0+(552630377/1000000000 : ℝ)*X 0 1+(49573731/156250000 : ℝ)*X 0 2+(4187922297/10000000000 : ℝ)*X 1 0+(552630377/1000000000 : ℝ)*X 1 1+(49573731/156250000 : ℝ)*X 1 2+(4187922297/10000000000 : ℝ)*X 2 0+(552630377/1000000000 : ℝ)*X 2 1+(49573731/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4684522583724282259689/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (83048401/100000000000000 : ℝ)*(base1) + (6740927/50000000000000 : ℝ)*(base16) + (705763973/100000000000000 : ℝ)*(base19) + (134985957/20000000000000 : ℝ)*(base23) + (13109513/10000000000000 : ℝ)*(upper3) + (155784039277419/25000000000000 : ℝ)*(major0) + (155784039277419/25000000000000 : ℝ)*(major1) + (155784039277419/25000000000000 : ℝ)*(major2) + (210911115266033/25000000000000 : ℝ)*(sp0) + (421822797675223/50000000000000 : ℝ)*(sp1) + (843645639666487/100000000000000 : ℝ)*(sp2) + (40262463250031/10000000000000 : ℝ)*(sp3) + (1936580541/100000000000000 : ℝ)*(sp4) + (1184137879/100000000000000 : ℝ)*(sp7) + (40262589968659/10000000000000 : ℝ)*(f.failure) + (843646314596273/100000000000000 : ℝ)*(f.sum) + (7936159527031/3125000000000000000000000000 : ℝ)*base65 + (6285108591719/6250000000000000000000000000 : ℝ)*base68 + (27921116208281/6250000000000000000000000000 : ℝ)*base69 + (11647166358281/6250000000000000000000000000 : ℝ)*base71 + (6514685658281/3125000000000000000000000000 : ℝ)*base73 + (40012119222969/6250000000000000000000000000 : ℝ)*base76 + (11752251933281/6250000000000000000000000000 : ℝ)*base77 + (24214078264531/6250000000000000000000000000 : ℝ)*base79 + (14084765102031/3125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (2351433/500000000000000000000 : ℝ)*base90 + (2351433/500000000000000000000 : ℝ)*base92 + (2351433/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79593778212933102471903/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (336013243/25000000000000 : ℝ)*(base19) + (1409087981/100000000000000 : ℝ)*(base23) + (52609223/100000000000000 : ℝ)*(base39) + (172510733/100000000000000 : ℝ)*(upper3) + (86029529/50000000000000 : ℝ)*(upper5) + (657584208084419/100000000000000 : ℝ)*(major0) + (657584208084419/100000000000000 : ℝ)*(major1) + (164396038868799/25000000000000 : ℝ)*(major2) + (3022598937/100000000000000 : ℝ)*(sp1) + (656719723/20000000000000 : ℝ)*(sp2) + (445142195674849/50000000000000 : ℝ)*(sp4) + (890280024697789/100000000000000 : ℝ)*(sp5) + (35611190050893/4000000000000 : ℝ)*(sp6) + (212441879979919/50000000000000 : ℝ)*(sp7) + (212441879979919/50000000000000 : ℝ)*(f.failure) + (890284443958921/100000000000000 : ℝ)*(f.sum) + (9783040973773/5000000000000000000000000000 : ℝ)*base66 + (49526920300349/6250000000000000000000000000 : ℝ)*base68 + (1586246232531/25000000000000000000000000000 : ℝ)*base69 + (14618326344099/6250000000000000000000000000 : ℝ)*base72 + (37038728183773/5000000000000000000000000000 : ℝ)*base74 + (63990396717469/25000000000000000000000000000 : ℝ)*base76 + (34306384942469/25000000000000000000000000000 : ℝ)*base78 + (114155091792469/25000000000000000000000000000 : ℝ)*base80 + (35150254817469/12500000000000000000000000000 : ℝ)*base82 + (16634947/2500000000000000000000 : ℝ)*base89 + (16634947/2500000000000000000000 : ℝ)*base91 + (16634947/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1343_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (711/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1679/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1343_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1343_s1_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-398645033/2000000000 : ℝ)*x 0 + (2820842637/5000000000 : ℝ)*x 1 + (5047682021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (398645033/2000000000 : ℝ)^4303 ≤ (12045215794393/100000000000000 : ℝ)^3279 := by
    have hnat : (398645033 : ℕ)^4303*100000000000000^3279 ≤ 12045215794393^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398645033 2000000000 12045215794393 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2820842637/5000000000 : ℝ)^4303 ≤ (47181988859429/100000000000000 : ℝ)^3279 := by
    have hnat : (2820842637 : ℕ)^4303*100000000000000^3279 ≤ 47181988859429^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820842637 5000000000 47181988859429 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5047682021/10000000000 : ℝ)^4303 ≤ (20386397665251/50000000000000 : ℝ)^3279 := by
    have hnat : (5047682021 : ℕ)^4303*50000000000000^3279 ≤ 20386397665251^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5047682021 10000000000 20386397665251 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-398645033/2000000000 : ℝ), (2820842637/5000000000 : ℝ), (5047682021/10000000000 : ℝ)] ![(12045215794393/100000000000000 : ℝ), (47181988859429/100000000000000 : ℝ), (20386397665251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-398645033/2000000000 : ℝ)|^4303 ≤ (12045215794393/100000000000000 : ℝ)^3279
        have hw : |(-398645033/2000000000 : ℝ)|=(398645033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2820842637/5000000000 : ℝ)|^4303 ≤ (47181988859429/100000000000000 : ℝ)^3279
        have hw : |(2820842637/5000000000 : ℝ)|=(2820842637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5047682021/10000000000 : ℝ)|^4303 ≤ (20386397665251/50000000000000 : ℝ)^3279
        have hw : |(5047682021/10000000000 : ℝ)|=(5047682021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s1_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (675701713/1250000000 : ℝ)*x 0 + (-28877151/125000000 : ℝ)*x 1 + (5047682081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675701713/1250000000 : ℝ)^4303 ≤ (5576029957017/12500000000000 : ℝ)^3279 := by
    have hnat : (675701713 : ℕ)^4303*12500000000000^3279 ≤ 5576029957017^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675701713 1250000000 5576029957017 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28877151/125000000 : ℝ)^4303 ≤ (1827370545059/12500000000000 : ℝ)^3279 := by
    have hnat : (28877151 : ℕ)^4303*12500000000000^3279 ≤ 1827370545059^3279*125000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28877151 125000000 1827370545059 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5047682081/10000000000 : ℝ)^4303 ≤ (20386397983253/50000000000000 : ℝ)^3279 := by
    have hnat : (5047682081 : ℕ)^4303*50000000000000^3279 ≤ 20386397983253^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5047682081 10000000000 20386397983253 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675701713/1250000000 : ℝ), (-28877151/125000000 : ℝ), (5047682081/10000000000 : ℝ)] ![(5576029957017/12500000000000 : ℝ), (1827370545059/12500000000000 : ℝ), (20386397983253/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675701713/1250000000 : ℝ)|^4303 ≤ (5576029957017/12500000000000 : ℝ)^3279
        have hw : |(675701713/1250000000 : ℝ)|=(675701713/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28877151/125000000 : ℝ)|^4303 ≤ (1827370545059/12500000000000 : ℝ)^3279
        have hw : |(-28877151/125000000 : ℝ)|=(28877151/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5047682081/10000000000 : ℝ)|^4303 ≤ (20386397983253/50000000000000 : ℝ)^3279
        have hw : |(5047682081/10000000000 : ℝ)|=(5047682081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s1_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1351403421/2500000000 : ℝ)*x 0 + (2523840921/5000000000 : ℝ)*x 1 + (-2310172411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351403421/2500000000 : ℝ)^4303 ≤ (44608239439551/100000000000000 : ℝ)^3279 := by
    have hnat : (1351403421 : ℕ)^4303*100000000000000^3279 ≤ 44608239439551^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351403421 2500000000 44608239439551 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2523840921/5000000000 : ℝ)^4303 ≤ (40772793433091/100000000000000 : ℝ)^3279 := by
    have hnat : (2523840921 : ℕ)^4303*100000000000000^3279 ≤ 40772793433091^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2523840921 5000000000 40772793433091 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2310172411/10000000000 : ℝ)^4303 ≤ (1461896710919/10000000000000 : ℝ)^3279 := by
    have hnat : (2310172411 : ℕ)^4303*10000000000000^3279 ≤ 1461896710919^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2310172411 10000000000 1461896710919 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351403421/2500000000 : ℝ), (2523840921/5000000000 : ℝ), (-2310172411/10000000000 : ℝ)] ![(44608239439551/100000000000000 : ℝ), (40772793433091/100000000000000 : ℝ), (1461896710919/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351403421/2500000000 : ℝ)|^4303 ≤ (44608239439551/100000000000000 : ℝ)^3279
        have hw : |(1351403421/2500000000 : ℝ)|=(1351403421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2523840921/5000000000 : ℝ)|^4303 ≤ (40772793433091/100000000000000 : ℝ)^3279
        have hw : |(2523840921/5000000000 : ℝ)|=(2523840921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2310172411/10000000000 : ℝ)|^4303 ≤ (1461896710919/10000000000000 : ℝ)^3279
        have hw : |(-2310172411/10000000000 : ℝ)|=(2310172411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s1_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2146064907/5000000000 : ℝ)*x 0 + (3711597143/10000000000 : ℝ)*x 1 + (4956247433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146064907/5000000000 : ℝ)^4303 ≤ (32957945432559/100000000000000 : ℝ)^3279 := by
    have hnat : (2146064907 : ℕ)^4303*100000000000000^3279 ≤ 32957945432559^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146064907 5000000000 32957945432559 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3711597143/10000000000 : ℝ)^4303 ≤ (27235718752089/100000000000000 : ℝ)^3279 := by
    have hnat : (3711597143 : ℕ)^4303*100000000000000^3279 ≤ 27235718752089^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3711597143 10000000000 27235718752089 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4956247433/10000000000 : ℝ)^4303 ≤ (4975791976193/12500000000000 : ℝ)^3279 := by
    have hnat : (4956247433 : ℕ)^4303*12500000000000^3279 ≤ 4975791976193^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4956247433 10000000000 4975791976193 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2146064907/5000000000 : ℝ), (3711597143/10000000000 : ℝ), (4956247433/10000000000 : ℝ)] ![(32957945432559/100000000000000 : ℝ), (27235718752089/100000000000000 : ℝ), (4975791976193/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2146064907/5000000000 : ℝ)|^4303 ≤ (32957945432559/100000000000000 : ℝ)^3279
        have hw : |(2146064907/5000000000 : ℝ)|=(2146064907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3711597143/10000000000 : ℝ)|^4303 ≤ (27235718752089/100000000000000 : ℝ)^3279
        have hw : |(3711597143/10000000000 : ℝ)|=(3711597143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4956247433/10000000000 : ℝ)|^4303 ≤ (4975791976193/12500000000000 : ℝ)^3279
        have hw : |(4956247433/10000000000 : ℝ)|=(4956247433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s1_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1993759743/10000000000 : ℝ)*x 0 + (1011025743/2000000000 : ℝ)*x 1 + (5634103317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993759743/10000000000 : ℝ)^4303 ≤ (6024727660769/50000000000000 : ℝ)^3279 := by
    have hnat : (1993759743 : ℕ)^4303*50000000000000^3279 ≤ 6024727660769^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993759743 10000000000 6024727660769 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011025743/2000000000 : ℝ)^4303 ≤ (159577144257/390625000000 : ℝ)^3279 := by
    have hnat : (1011025743 : ℕ)^4303*390625000000^3279 ≤ 159577144257^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011025743 2000000000 159577144257 390625000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5634103317/10000000000 : ℝ)^4303 ≤ (47098795729757/100000000000000 : ℝ)^3279 := by
    have hnat : (5634103317 : ℕ)^4303*100000000000000^3279 ≤ 47098795729757^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634103317 10000000000 47098795729757 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1993759743/10000000000 : ℝ), (1011025743/2000000000 : ℝ), (5634103317/10000000000 : ℝ)] ![(6024727660769/50000000000000 : ℝ), (159577144257/390625000000 : ℝ), (47098795729757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1993759743/10000000000 : ℝ)|^4303 ≤ (6024727660769/50000000000000 : ℝ)^3279
        have hw : |(-1993759743/10000000000 : ℝ)|=(1993759743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011025743/2000000000 : ℝ)|^4303 ≤ (159577144257/390625000000 : ℝ)^3279
        have hw : |(1011025743/2000000000 : ℝ)|=(1011025743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5634103317/10000000000 : ℝ)|^4303 ≤ (47098795729757/100000000000000 : ℝ)^3279
        have hw : |(5634103317/10000000000 : ℝ)|=(5634103317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s1_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656433127/1250000000 : ℝ)*x 0 + (-861875769/5000000000 : ℝ)*x 1 + (70426281/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656433127/1250000000 : ℝ)^4303 ≤ (42946400886289/100000000000000 : ℝ)^3279 := by
    have hnat : (656433127 : ℕ)^4303*100000000000000^3279 ≤ 42946400886289^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656433127 1250000000 42946400886289 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (861875769/5000000000 : ℝ)^4303 ≤ (9954812547463/100000000000000 : ℝ)^3279 := by
    have hnat : (861875769 : ℕ)^4303*100000000000000^3279 ≤ 9954812547463^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861875769 5000000000 9954812547463 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (70426281/125000000 : ℝ)^4303 ≤ (11774696636923/25000000000000 : ℝ)^3279 := by
    have hnat : (70426281 : ℕ)^4303*25000000000000^3279 ≤ 11774696636923^3279*125000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70426281 125000000 11774696636923 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656433127/1250000000 : ℝ), (-861875769/5000000000 : ℝ), (70426281/125000000 : ℝ)] ![(42946400886289/100000000000000 : ℝ), (9954812547463/100000000000000 : ℝ), (11774696636923/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656433127/1250000000 : ℝ)|^4303 ≤ (42946400886289/100000000000000 : ℝ)^3279
        have hw : |(656433127/1250000000 : ℝ)|=(656433127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-861875769/5000000000 : ℝ)|^4303 ≤ (9954812547463/100000000000000 : ℝ)^3279
        have hw : |(-861875769/5000000000 : ℝ)|=(861875769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(70426281/125000000 : ℝ)|^4303 ≤ (11774696636923/25000000000000 : ℝ)^3279
        have hw : |(70426281/125000000 : ℝ)|=(70426281/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s1_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262573211/500000000 : ℝ)*x 0 + (5634102273/10000000000 : ℝ)*x 1 + (-861876483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262573211/500000000 : ℝ)^4303 ≤ (8589278468741/20000000000000 : ℝ)^3279 := by
    have hnat : (262573211 : ℕ)^4303*20000000000000^3279 ≤ 8589278468741^3279*500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262573211 500000000 8589278468741 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5634102273/10000000000 : ℝ)^4303 ≤ (23549392138429/50000000000000 : ℝ)^3279 := by
    have hnat : (5634102273 : ℕ)^4303*50000000000000^3279 ≤ 23549392138429^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5634102273 10000000000 23549392138429 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861876483/5000000000 : ℝ)^4303 ≤ (995482336969/10000000000000 : ℝ)^3279 := by
    have hnat : (861876483 : ℕ)^4303*10000000000000^3279 ≤ 995482336969^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861876483 5000000000 995482336969 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262573211/500000000 : ℝ), (5634102273/10000000000 : ℝ), (-861876483/5000000000 : ℝ)] ![(8589278468741/20000000000000 : ℝ), (23549392138429/50000000000000 : ℝ), (995482336969/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262573211/500000000 : ℝ)|^4303 ≤ (8589278468741/20000000000000 : ℝ)^3279
        have hw : |(262573211/500000000 : ℝ)|=(262573211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5634102273/10000000000 : ℝ)|^4303 ≤ (23549392138429/50000000000000 : ℝ)^3279
        have hw : |(5634102273/10000000000 : ℝ)|=(5634102273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-861876483/5000000000 : ℝ)|^4303 ≤ (995482336969/10000000000000 : ℝ)^3279
        have hw : |(-861876483/5000000000 : ℝ)|=(861876483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s1_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1073312311/2500000000 : ℝ)*x 0 + (617580393/1250000000 : ℝ)*x 1 + (931871447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073312311/2500000000 : ℝ)^4303 ≤ (32969226023151/100000000000000 : ℝ)^3279 := by
    have hnat : (1073312311 : ℕ)^4303*100000000000000^3279 ≤ 32969226023151^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073312311 2500000000 32969226023151 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (617580393/1250000000 : ℝ)^4303 ≤ (19820975926849/50000000000000 : ℝ)^3279 := by
    have hnat : (617580393 : ℕ)^4303*50000000000000^3279 ≤ 19820975926849^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      617580393 1250000000 19820975926849 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931871447/2500000000 : ℝ)^4303 ≤ (2738882210919/10000000000000 : ℝ)^3279 := by
    have hnat : (931871447 : ℕ)^4303*10000000000000^3279 ≤ 2738882210919^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931871447 2500000000 2738882210919 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1073312311/2500000000 : ℝ), (617580393/1250000000 : ℝ), (931871447/2500000000 : ℝ)] ![(32969226023151/100000000000000 : ℝ), (19820975926849/50000000000000 : ℝ), (2738882210919/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1073312311/2500000000 : ℝ)|^4303 ≤ (32969226023151/100000000000000 : ℝ)^3279
        have hw : |(1073312311/2500000000 : ℝ)|=(1073312311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(617580393/1250000000 : ℝ)|^4303 ≤ (19820975926849/50000000000000 : ℝ)^3279
        have hw : |(617580393/1250000000 : ℝ)|=(617580393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(931871447/2500000000 : ℝ)|^4303 ≤ (2738882210919/10000000000000 : ℝ)^3279
        have hw : |(931871447/2500000000 : ℝ)|=(931871447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1679/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6899/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9727/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1679/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1679/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (711/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1679/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1679/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (711/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1679/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1679/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (711/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (711/50000 : ℝ) ^ (2151/512 : ℝ) ≤ (173785578559/10000000000000000000 : ℝ) := by
    have hpowers : (711/50000 : ℝ)^2151 ≤ (173785578559/10000000000000000000 : ℝ)^512 := by
      have hnat : (711 : ℕ)^2151*10000000000000000000^512 ≤ 173785578559^512*50000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        711 50000 173785578559 10000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (711/50000 : ℝ)) (X := (173785578559/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1679/6250 : ℝ) ^ (2151/512 : ℝ) ≤ (199902356931490833/50000000000000000000 : ℝ) := by
    have hpowers : (1679/6250 : ℝ)^2151 ≤ (199902356931490833/50000000000000000000 : ℝ)^512 := by
      have hnat : (1679 : ℕ)^2151*50000000000000000000^512 ≤ 199902356931490833^512*6250^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1679 6250 199902356931490833 50000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1679/6250 : ℝ)) (X := (199902356931490833/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000000173785578559/5000000000000000000 : ℝ) ≤ (10000000082731953/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (5000000173785578559/5000000000000000000 : ℝ)^512 ≤ (10000000082731953/10000000000000000 : ℝ)^2151 := by
      have hnat : (5000000173785578559 : ℕ)^512*10000000000000000^2151 ≤ 10000000082731953^2151*5000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000000173785578559 5000000000000000000 10000000082731953 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000082731953/10000000000000000 : ℝ)) (X := (5000000173785578559/5000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12549975806464845907/12500000000000000000 : ℝ) ≤ (5004751042119769/5000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (12549975806464845907/12500000000000000000 : ℝ)^512 ≤ (5004751042119769/5000000000000000 : ℝ)^2151 := by
      have hnat : (12549975806464845907 : ℕ)^512*5000000000000000^2151 ≤ 5004751042119769^2151*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12549975806464845907 12500000000000000000 5004751042119769 5000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004751042119769/5000000000000000 : ℝ)) (X := (12549975806464845907/12500000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25199902356931490833/25000000000000000000 : ℝ) ≤ (10019004085747123/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (25199902356931490833/25000000000000000000 : ℝ)^512 ≤ (10019004085747123/10000000000000000 : ℝ)^2151 := by
      have hnat : (25199902356931490833 : ℕ)^512*10000000000000000^2151 ≤ 10019004085747123^2151*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25199902356931490833 25000000000000000000 10019004085747123 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10019004085747123/10000000000000000 : ℝ)) (X := (25199902356931490833/25000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(173785578559/10000000000000000000 : ℝ) ≤ ((127196489206289388243/127210000000000000000 : ℝ)+2*(1900400301517/508840000000000 : ℝ)*(711/50000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (127196489206289388243/127210000000000000000 : ℝ)+2*(1900400301517/508840000000000 : ℝ)*(711/50000 : ℝ)=(10000000082731953/10000000000000000 : ℝ) by norm_num, show 1+2*(173785578559/10000000000000000000 : ℝ)=(5000000173785578559/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(199902356931490833/50000000000000000000 : ℝ)+(173785578559/10000000000000000000 : ℝ) ≤ ((127196489206289388243/127210000000000000000 : ℝ)+(1900400301517/508840000000000 : ℝ)*((1679/6250 : ℝ)+(711/50000 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (127196489206289388243/127210000000000000000 : ℝ)+(1900400301517/508840000000000 : ℝ)*((1679/6250 : ℝ)+(711/50000 : ℝ))=(5004751042119769/5000000000000000 : ℝ) by norm_num, show 1+(199902356931490833/50000000000000000000 : ℝ)+(173785578559/10000000000000000000 : ℝ)=(12549975806464845907/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(199902356931490833/50000000000000000000 : ℝ) ≤ ((127196489206289388243/127210000000000000000 : ℝ)+2*(1900400301517/508840000000000 : ℝ)*(1679/6250 : ℝ))^(2151/512 : ℝ) := by
    rw [show (127196489206289388243/127210000000000000000 : ℝ)+2*(1900400301517/508840000000000 : ℝ)*(1679/6250 : ℝ)=(10019004085747123/10000000000000000 : ℝ) by norm_num, show 1+2*(199902356931490833/50000000000000000000 : ℝ)=(25199902356931490833/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (127196489206289388243/127210000000000000000 : ℝ)*(X 1 0+X 2 0)+(1900400301517/508840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (711/50000 : ℝ)) (hi := (1679/6250 : ℝ)) (c := (127196489206289388243/127210000000000000000 : ℝ)) (alpha := (1900400301517/508840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (127196489206289388243/127210000000000000000 : ℝ)*(X 0 1+X 2 1)+(1900400301517/508840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (711/50000 : ℝ)) (hi := (1679/6250 : ℝ)) (c := (127196489206289388243/127210000000000000000 : ℝ)) (alpha := (1900400301517/508840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (127196489206289388243/127210000000000000000 : ℝ)*(X 0 2+X 1 2)+(1900400301517/508840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (711/50000 : ℝ)) (hi := (1679/6250 : ℝ)) (c := (127196489206289388243/127210000000000000000 : ℝ)) (alpha := (1900400301517/508840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-398645033/2000000000 : ℝ)*X 0 0+(2820842637/5000000000 : ℝ)*X 0 1+(5047682021/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((675701713/1250000000 : ℝ)*X 1 0+(-28877151/125000000 : ℝ)*X 1 1+(5047682081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1351403421/2500000000 : ℝ)*X 2 0+(2523840921/5000000000 : ℝ)*X 2 1+(-2310172411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2146064907/5000000000 : ℝ)*X 0 0+(3711597143/10000000000 : ℝ)*X 0 1+(4956247433/10000000000 : ℝ)*X 0 2+(2146064907/5000000000 : ℝ)*X 1 0+(3711597143/10000000000 : ℝ)*X 1 1+(4956247433/10000000000 : ℝ)*X 1 2+(2146064907/5000000000 : ℝ)*X 2 0+(3711597143/10000000000 : ℝ)*X 2 1+(4956247433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1993759743/10000000000 : ℝ)*X 0 0+(1011025743/2000000000 : ℝ)*X 0 1+(5634103317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((656433127/1250000000 : ℝ)*X 1 0+(-861875769/5000000000 : ℝ)*X 1 1+(70426281/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262573211/500000000 : ℝ)*X 2 0+(5634102273/10000000000 : ℝ)*X 2 1+(-861876483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1073312311/2500000000 : ℝ)*X 0 0+(617580393/1250000000 : ℝ)*X 0 1+(931871447/2500000000 : ℝ)*X 0 2+(1073312311/2500000000 : ℝ)*X 1 0+(617580393/1250000000 : ℝ)*X 1 1+(931871447/2500000000 : ℝ)*X 1 2+(1073312311/2500000000 : ℝ)*X 2 0+(617580393/1250000000 : ℝ)*X 2 1+(931871447/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6200625974819073715253100249/795062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14042947/20000000000000 : ℝ)*(base1) + (1243651329/100000000000000 : ℝ)*(base19) + (6187113/500000000000 : ℝ)*(base23) + (43902579/20000000000000 : ℝ)*(upper3) + (82120357/100000000000000 : ℝ)*(upper5) + (310868954468119/25000000000000 : ℝ)*(major0) + (310868954468119/25000000000000 : ℝ)*(major1) + (310868954468119/25000000000000 : ℝ)*(major2) + (420875053701371/25000000000000 : ℝ)*(sp0) + (1683505228159407/100000000000000 : ℝ)*(sp1) + (210438154298517/12500000000000 : ℝ)*(sp2) + (803441315323781/100000000000000 : ℝ)*(sp3) + (6327219987/100000000000000 : ℝ)*(sp4) + (1759215907/50000000000000 : ℝ)*(sp7) + (80344490397033/10000000000000 : ℝ)*(f.failure) + (105219154488171/6250000000000 : ℝ)*(f.sum) + (6826005570617/12721000000000000000000000000 : ℝ)*base65 + (11763247496932674917/3180250000000000000000000000000000 : ℝ)*base67 + (10835398657535674917/3180250000000000000000000000000000 : ℝ)*base69 + (655815300171825083/3180250000000000000000000000000000 : ℝ)*base72 + (60643249496627/12721000000000000000000000000 : ℝ)*base73 + (12167650147734674917/3180250000000000000000000000000000 : ℝ)*base75 + (5217662817674174917/3180250000000000000000000000000000 : ℝ)*base77 + (12384804490254924917/3180250000000000000000000000000000 : ℝ)*base79 + (56637872566857/12721000000000000000000000000 : ℝ)*base81 + (3166571/500000000000000000000 : ℝ)*base90 + (3166571/500000000000000000000 : ℝ)*base92 + (3166571/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28710906468011184272707477767/3180250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49089631/4000000000000 : ℝ)*(base19) + (806111137/100000000000000 : ℝ)*(base23) + (2971453/50000000000000 : ℝ)*(upper2) + (41659283/100000000000000 : ℝ)*(upper3) + (234966067/100000000000000 : ℝ)*(upper5) + (637871746830341/50000000000000 : ℝ)*(major0) + (637871746830341/50000000000000 : ℝ)*(major1) + (637871746830341/50000000000000 : ℝ)*(major2) + (5961174463/100000000000000 : ℝ)*(sp1) + (36937153/25000000000000 : ℝ)*(sp2) + (431798181059893/25000000000000 : ℝ)*(sp4) + (1727185535824333/100000000000000 : ℝ)*(sp5) + (863595885189911/50000000000000 : ℝ)*(sp6) + (412146981076273/50000000000000 : ℝ)*(sp7) + (412146981076273/50000000000000 : ℝ)*(f.failure) + (431798181059893/25000000000000 : ℝ)*(f.sum) + (9116582998091/12721000000000000000000000000 : ℝ)*base66 + (54757068457716669137/6360500000000000000000000000000000 : ℝ)*base68 + (12256983235180669137/6360500000000000000000000000000000 : ℝ)*base70 + (10372837329666669137/6360500000000000000000000000000000 : ℝ)*base72 + (28870415859733/12721000000000000000000000000 : ℝ)*base74 + (31921633077530169137/6360500000000000000000000000000000 : ℝ)*base76 + (18409330148230669137/6360500000000000000000000000000000 : ℝ)*base78 + (43436197244881669137/6360500000000000000000000000000000 : ℝ)*base80 + (54590243060553/12721000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13823549/2500000000000000000000 : ℝ)*base89 + (13823549/2500000000000000000000 : ℝ)*base91 + (13823549/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1343_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1679/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (711/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6899/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9727/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1343_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1343_s2_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2033293667/10000000000 : ℝ)*x 0 + (5479476843/10000000000 : ℝ)*x 1 + (5184222703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033293667/10000000000 : ℝ)^4303 ≤ (6181981400263/50000000000000 : ℝ)^3279 := by
    have hnat : (2033293667 : ℕ)^4303*50000000000000^3279 ≤ 6181981400263^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033293667 10000000000 6181981400263 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5479476843/10000000000 : ℝ)^4303 ≤ (45409826366317/100000000000000 : ℝ)^3279 := by
    have hnat : (5479476843 : ℕ)^4303*100000000000000^3279 ≤ 45409826366317^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5479476843 10000000000 45409826366317 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184222703/10000000000 : ℝ)^4303 ≤ (10556552706559/25000000000000 : ℝ)^3279 := by
    have hnat : (5184222703 : ℕ)^4303*25000000000000^3279 ≤ 10556552706559^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184222703 10000000000 10556552706559 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2033293667/10000000000 : ℝ), (5479476843/10000000000 : ℝ), (5184222703/10000000000 : ℝ)] ![(6181981400263/50000000000000 : ℝ), (45409826366317/100000000000000 : ℝ), (10556552706559/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2033293667/10000000000 : ℝ)|^4303 ≤ (6181981400263/50000000000000 : ℝ)^3279
        have hw : |(-2033293667/10000000000 : ℝ)|=(2033293667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5479476843/10000000000 : ℝ)|^4303 ≤ (45409826366317/100000000000000 : ℝ)^3279
        have hw : |(5479476843/10000000000 : ℝ)|=(5479476843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184222703/10000000000 : ℝ)|^4303 ≤ (10556552706559/25000000000000 : ℝ)^3279
        have hw : |(5184222703/10000000000 : ℝ)|=(5184222703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s2_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682941611/5000000000 : ℝ)*x 0 + (-1092922573/5000000000 : ℝ)*x 1 + (1036844619/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682941611/5000000000 : ℝ)^4303 ≤ (44178481333003/100000000000000 : ℝ)^3279 := by
    have hnat : (2682941611 : ℕ)^4303*100000000000000^3279 ≤ 44178481333003^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682941611 5000000000 44178481333003 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092922573/5000000000 : ℝ)^4303 ≤ (13595303645241/100000000000000 : ℝ)^3279 := by
    have hnat : (1092922573 : ℕ)^4303*100000000000000^3279 ≤ 13595303645241^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092922573 5000000000 13595303645241 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036844619/2000000000 : ℝ)^4303 ≤ (527827687703/1250000000000 : ℝ)^3279 := by
    have hnat : (1036844619 : ℕ)^4303*1250000000000^3279 ≤ 527827687703^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036844619 2000000000 527827687703 1250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682941611/5000000000 : ℝ), (-1092922573/5000000000 : ℝ), (1036844619/2000000000 : ℝ)] ![(44178481333003/100000000000000 : ℝ), (13595303645241/100000000000000 : ℝ), (527827687703/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682941611/5000000000 : ℝ)|^4303 ≤ (44178481333003/100000000000000 : ℝ)^3279
        have hw : |(2682941611/5000000000 : ℝ)|=(2682941611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1092922573/5000000000 : ℝ)|^4303 ≤ (13595303645241/100000000000000 : ℝ)^3279
        have hw : |(-1092922573/5000000000 : ℝ)|=(1092922573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036844619/2000000000 : ℝ)|^4303 ≤ (527827687703/1250000000000 : ℝ)^3279
        have hw : |(1036844619/2000000000 : ℝ)|=(1036844619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s2_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682941653/5000000000 : ℝ)*x 0 + (2592111499/5000000000 : ℝ)*x 1 + (-2185845161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682941653/5000000000 : ℝ)^4303 ≤ (4417848224057/10000000000000 : ℝ)^3279 := by
    have hnat : (2682941653 : ℕ)^4303*10000000000000^3279 ≤ 4417848224057^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682941653 5000000000 4417848224057 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592111499/5000000000 : ℝ)^4303 ≤ (10556553494857/25000000000000 : ℝ)^3279 := by
    have hnat : (2592111499 : ℕ)^4303*25000000000000^3279 ≤ 10556553494857^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592111499 5000000000 10556553494857 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185845161/10000000000 : ℝ)^4303 ≤ (1699412970959/12500000000000 : ℝ)^3279 := by
    have hnat : (2185845161 : ℕ)^4303*12500000000000^3279 ≤ 1699412970959^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185845161 10000000000 1699412970959 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682941653/5000000000 : ℝ), (2592111499/5000000000 : ℝ), (-2185845161/10000000000 : ℝ)] ![(4417848224057/10000000000000 : ℝ), (10556553494857/25000000000000 : ℝ), (1699412970959/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682941653/5000000000 : ℝ)|^4303 ≤ (4417848224057/10000000000000 : ℝ)^3279
        have hw : |(2682941653/5000000000 : ℝ)|=(2682941653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592111499/5000000000 : ℝ)|^4303 ≤ (10556553494857/25000000000000 : ℝ)^3279
        have hw : |(2592111499/5000000000 : ℝ)|=(2592111499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2185845161/10000000000 : ℝ)|^4303 ≤ (1699412970959/12500000000000 : ℝ)^3279
        have hw : |(-2185845161/10000000000 : ℝ)|=(2185845161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s2_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270009423/625000000 : ℝ)*x 0 + (1005284599/2500000000 : ℝ)*x 1 + (4639801511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270009423/625000000 : ℝ)^4303 ≤ (33240590855127/100000000000000 : ℝ)^3279 := by
    have hnat : (270009423 : ℕ)^4303*100000000000000^3279 ≤ 33240590855127^3279*625000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270009423 625000000 33240590855127 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005284599/2500000000 : ℝ)^4303 ≤ (30254574167331/100000000000000 : ℝ)^3279 := by
    have hnat : (1005284599 : ℕ)^4303*100000000000000^3279 ≤ 30254574167331^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005284599 2500000000 30254574167331 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4639801511/10000000000 : ℝ)^4303 ≤ (1825241748273/5000000000000 : ℝ)^3279 := by
    have hnat : (4639801511 : ℕ)^4303*5000000000000^3279 ≤ 1825241748273^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4639801511 10000000000 1825241748273 5000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270009423/625000000 : ℝ), (1005284599/2500000000 : ℝ), (4639801511/10000000000 : ℝ)] ![(33240590855127/100000000000000 : ℝ), (30254574167331/100000000000000 : ℝ), (1825241748273/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270009423/625000000 : ℝ)|^4303 ≤ (33240590855127/100000000000000 : ℝ)^3279
        have hw : |(270009423/625000000 : ℝ)|=(270009423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1005284599/2500000000 : ℝ)|^4303 ≤ (30254574167331/100000000000000 : ℝ)^3279
        have hw : |(1005284599/2500000000 : ℝ)|=(1005284599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4639801511/10000000000 : ℝ)|^4303 ≤ (1825241748273/5000000000000 : ℝ)^3279
        have hw : |(4639801511/10000000000 : ℝ)|=(4639801511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s2_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2033359339/10000000000 : ℝ)*x 0 + (129651823/250000000 : ℝ)*x 1 + (5477609967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2033359339/10000000000 : ℝ)^4303 ≤ (1236448684717/10000000000000 : ℝ)^3279 := by
    have hnat : (2033359339 : ℕ)^4303*10000000000000^3279 ≤ 1236448684717^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2033359339 10000000000 1236448684717 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129651823/250000000 : ℝ)^4303 ≤ (5280748562779/12500000000000 : ℝ)^3279 := by
    have hnat : (129651823 : ℕ)^4303*12500000000000^3279 ≤ 5280748562779^3279*250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129651823 250000000 5280748562779 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5477609967/10000000000 : ℝ)^4303 ≤ (45389524636633/100000000000000 : ℝ)^3279 := by
    have hnat : (5477609967 : ℕ)^4303*100000000000000^3279 ≤ 45389524636633^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5477609967 10000000000 45389524636633 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2033359339/10000000000 : ℝ), (129651823/250000000 : ℝ), (5477609967/10000000000 : ℝ)] ![(1236448684717/10000000000000 : ℝ), (5280748562779/12500000000000 : ℝ), (45389524636633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2033359339/10000000000 : ℝ)|^4303 ≤ (1236448684717/10000000000000 : ℝ)^3279
        have hw : |(-2033359339/10000000000 : ℝ)|=(2033359339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129651823/250000000 : ℝ)|^4303 ≤ (5280748562779/12500000000000 : ℝ)^3279
        have hw : |(129651823/250000000 : ℝ)|=(129651823/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5477609967/10000000000 : ℝ)|^4303 ≤ (45389524636633/100000000000000 : ℝ)^3279
        have hw : |(5477609967/10000000000 : ℝ)|=(5477609967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s2_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289773249/10000000000 : ℝ)*x 0 + (-946228987/5000000000 : ℝ)*x 1 + (1369402491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289773249/10000000000 : ℝ)^4303 ≤ (43357988144583/100000000000000 : ℝ)^3279 := by
    have hnat : (5289773249 : ℕ)^4303*100000000000000^3279 ≤ 43357988144583^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289773249 10000000000 43357988144583 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946228987/5000000000 : ℝ)^4303 ≤ (11252487242351/100000000000000 : ℝ)^3279 := by
    have hnat : (946228987 : ℕ)^4303*100000000000000^3279 ≤ 11252487242351^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946228987 5000000000 11252487242351 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369402491/2500000000 : ℝ)^4303 ≤ (45389524604011/100000000000000 : ℝ)^3279 := by
    have hnat : (1369402491 : ℕ)^4303*100000000000000^3279 ≤ 45389524604011^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369402491 2500000000 45389524604011 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289773249/10000000000 : ℝ), (-946228987/5000000000 : ℝ), (1369402491/2500000000 : ℝ)] ![(43357988144583/100000000000000 : ℝ), (11252487242351/100000000000000 : ℝ), (45389524604011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289773249/10000000000 : ℝ)|^4303 ≤ (43357988144583/100000000000000 : ℝ)^3279
        have hw : |(5289773249/10000000000 : ℝ)|=(5289773249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-946228987/5000000000 : ℝ)|^4303 ≤ (11252487242351/100000000000000 : ℝ)^3279
        have hw : |(-946228987/5000000000 : ℝ)|=(946228987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369402491/2500000000 : ℝ)|^4303 ≤ (45389524604011/100000000000000 : ℝ)^3279
        have hw : |(1369402491/2500000000 : ℝ)|=(1369402491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s2_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644886631/5000000000 : ℝ)*x 0 + (2738804987/5000000000 : ℝ)*x 1 + (-946228971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644886631/5000000000 : ℝ)^4303 ≤ (21678994142207/50000000000000 : ℝ)^3279 := by
    have hnat : (2644886631 : ℕ)^4303*50000000000000^3279 ≤ 21678994142207^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644886631 5000000000 21678994142207 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2738804987/5000000000 : ℝ)^4303 ≤ (2836845294547/6250000000000 : ℝ)^3279 := by
    have hnat : (2738804987 : ℕ)^4303*6250000000000^3279 ≤ 2836845294547^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2738804987 5000000000 2836845294547 6250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946228971/5000000000 : ℝ)^4303 ≤ (562624349633/5000000000000 : ℝ)^3279 := by
    have hnat : (946228971 : ℕ)^4303*5000000000000^3279 ≤ 562624349633^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946228971 5000000000 562624349633 5000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644886631/5000000000 : ℝ), (2738804987/5000000000 : ℝ), (-946228971/5000000000 : ℝ)] ![(21678994142207/50000000000000 : ℝ), (2836845294547/6250000000000 : ℝ), (562624349633/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644886631/5000000000 : ℝ)|^4303 ≤ (21678994142207/50000000000000 : ℝ)^3279
        have hw : |(2644886631/5000000000 : ℝ)|=(2644886631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2738804987/5000000000 : ℝ)|^4303 ≤ (2836845294547/6250000000000 : ℝ)^3279
        have hw : |(2738804987/5000000000 : ℝ)|=(2738804987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-946228971/5000000000 : ℝ)|^4303 ≤ (562624349633/5000000000000 : ℝ)^3279
        have hw : |(-946228971/5000000000 : ℝ)|=(946228971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s2_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320288731/10000000000 : ℝ)*x 0 + (1158981323/2500000000 : ℝ)*x 1 + (1006262391/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320288731/10000000000 : ℝ)^4303 ≤ (6648396779647/20000000000000 : ℝ)^3279 := by
    have hnat : (4320288731 : ℕ)^4303*20000000000000^3279 ≤ 6648396779647^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320288731 10000000000 6648396779647 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1158981323/2500000000 : ℝ)^4303 ≤ (36464819068563/100000000000000 : ℝ)^3279 := by
    have hnat : (1158981323 : ℕ)^4303*100000000000000^3279 ≤ 36464819068563^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1158981323 2500000000 36464819068563 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006262391/2500000000 : ℝ)^4303 ≤ (7573299255351/25000000000000 : ℝ)^3279 := by
    have hnat : (1006262391 : ℕ)^4303*25000000000000^3279 ≤ 7573299255351^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006262391 2500000000 7573299255351 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320288731/10000000000 : ℝ), (1158981323/2500000000 : ℝ), (1006262391/2500000000 : ℝ)] ![(6648396779647/20000000000000 : ℝ), (36464819068563/100000000000000 : ℝ), (7573299255351/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320288731/10000000000 : ℝ)|^4303 ≤ (6648396779647/20000000000000 : ℝ)^3279
        have hw : |(4320288731/10000000000 : ℝ)|=(4320288731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1158981323/2500000000 : ℝ)|^4303 ≤ (36464819068563/100000000000000 : ℝ)^3279
        have hw : |(1158981323/2500000000 : ℝ)|=(1158981323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006262391/2500000000 : ℝ)|^4303 ≤ (7573299255351/25000000000000 : ℝ)^3279
        have hw : |(1006262391/2500000000 : ℝ)|=(1006262391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9727/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4929/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (161/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9727/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9727/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6899/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9727/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9727/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6899/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9727/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9727/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6899/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6899/100000 : ℝ) ^ (2151/512 : ℝ) ≤ (264588526041603/20000000000000000000 : ℝ) := by
    have hpowers : (6899/100000 : ℝ)^2151 ≤ (264588526041603/20000000000000000000 : ℝ)^512 := by
      have hnat : (6899 : ℕ)^2151*20000000000000000000^512 ≤ 264588526041603^512*100000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6899 100000 264588526041603 20000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6899/100000 : ℝ)) (X := (264588526041603/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9727/50000 : ℝ) ^ (2151/512 : ℝ) ≤ (51519808505356941/50000000000000000000 : ℝ) := by
    have hpowers : (9727/50000 : ℝ)^2151 ≤ (51519808505356941/50000000000000000000 : ℝ)^512 := by
      have hnat : (9727 : ℕ)^2151*50000000000000000000^512 ≤ 51519808505356941^512*50000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9727 50000 51519808505356941 50000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9727/50000 : ℝ)) (X := (51519808505356941/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000264588526041603/10000000000000000000 : ℝ) ≤ (10000062979060793/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (10000264588526041603/10000000000000000000 : ℝ)^512 ≤ (10000062979060793/10000000000000000 : ℝ)^2151 := by
      have hnat : (10000264588526041603 : ℕ)^512*10000000000000000^2151 ≤ 10000062979060793^2151*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000264588526041603 10000000000000000000 10000062979060793 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000062979060793/10000000000000000 : ℝ)) (X := (10000264588526041603/10000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100104362559640921897/100000000000000000000 : ℝ) ≤ (10002483142631353/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (100104362559640921897/100000000000000000000 : ℝ)^512 ≤ (10002483142631353/10000000000000000 : ℝ)^2151 := by
      have hnat : (100104362559640921897 : ℕ)^512*10000000000000000^2151 ≤ 10002483142631353^2151*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100104362559640921897 100000000000000000000 10002483142631353 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002483142631353/10000000000000000 : ℝ)) (X := (100104362559640921897/100000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25051519808505356941/25000000000000000000 : ℝ) ≤ (10004903306201913/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (25051519808505356941/25000000000000000000 : ℝ)^512 ≤ (10004903306201913/10000000000000000 : ℝ)^2151 := by
      have hnat : (25051519808505356941 : ℕ)^512*10000000000000000^2151 ≤ 10004903306201913^2151*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25051519808505356941 25000000000000000000 10004903306201913 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004903306201913/10000000000000000 : ℝ)) (X := (25051519808505356941/25000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(264588526041603/20000000000000000000 : ℝ) ≤ ((25103479457032333847/25110000000000000000 : ℝ)+2*(3781505579/1961718750000 : ℝ)*(6899/100000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (25103479457032333847/25110000000000000000 : ℝ)+2*(3781505579/1961718750000 : ℝ)*(6899/100000 : ℝ)=(10000062979060793/10000000000000000 : ℝ) by norm_num, show 1+2*(264588526041603/20000000000000000000 : ℝ)=(10000264588526041603/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(51519808505356941/50000000000000000000 : ℝ)+(264588526041603/20000000000000000000 : ℝ) ≤ ((25103479457032333847/25110000000000000000 : ℝ)+(3781505579/1961718750000 : ℝ)*((9727/50000 : ℝ)+(6899/100000 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (25103479457032333847/25110000000000000000 : ℝ)+(3781505579/1961718750000 : ℝ)*((9727/50000 : ℝ)+(6899/100000 : ℝ))=(10002483142631353/10000000000000000 : ℝ) by norm_num, show 1+(51519808505356941/50000000000000000000 : ℝ)+(264588526041603/20000000000000000000 : ℝ)=(100104362559640921897/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(51519808505356941/50000000000000000000 : ℝ) ≤ ((25103479457032333847/25110000000000000000 : ℝ)+2*(3781505579/1961718750000 : ℝ)*(9727/50000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (25103479457032333847/25110000000000000000 : ℝ)+2*(3781505579/1961718750000 : ℝ)*(9727/50000 : ℝ)=(10004903306201913/10000000000000000 : ℝ) by norm_num, show 1+2*(51519808505356941/50000000000000000000 : ℝ)=(25051519808505356941/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25103479457032333847/25110000000000000000 : ℝ)*(X 1 0+X 2 0)+(3781505579/1961718750000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (6899/100000 : ℝ)) (hi := (9727/50000 : ℝ)) (c := (25103479457032333847/25110000000000000000 : ℝ)) (alpha := (3781505579/1961718750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25103479457032333847/25110000000000000000 : ℝ)*(X 0 1+X 2 1)+(3781505579/1961718750000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (6899/100000 : ℝ)) (hi := (9727/50000 : ℝ)) (c := (25103479457032333847/25110000000000000000 : ℝ)) (alpha := (3781505579/1961718750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25103479457032333847/25110000000000000000 : ℝ)*(X 0 2+X 1 2)+(3781505579/1961718750000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (6899/100000 : ℝ)) (hi := (9727/50000 : ℝ)) (c := (25103479457032333847/25110000000000000000 : ℝ)) (alpha := (3781505579/1961718750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2033293667/10000000000 : ℝ)*X 0 0+(5479476843/10000000000 : ℝ)*X 0 1+(5184222703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2682941611/5000000000 : ℝ)*X 1 0+(-1092922573/5000000000 : ℝ)*X 1 1+(1036844619/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2682941653/5000000000 : ℝ)*X 2 0+(2592111499/5000000000 : ℝ)*X 2 1+(-2185845161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270009423/625000000 : ℝ)*X 0 0+(1005284599/2500000000 : ℝ)*X 0 1+(4639801511/10000000000 : ℝ)*X 0 2+(270009423/625000000 : ℝ)*X 1 0+(1005284599/2500000000 : ℝ)*X 1 1+(4639801511/10000000000 : ℝ)*X 1 2+(270009423/625000000 : ℝ)*X 2 0+(1005284599/2500000000 : ℝ)*X 2 1+(4639801511/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2033359339/10000000000 : ℝ)*X 0 0+(129651823/250000000 : ℝ)*X 0 1+(5477609967/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289773249/10000000000 : ℝ)*X 1 0+(-946228987/5000000000 : ℝ)*X 1 1+(1369402491/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644886631/5000000000 : ℝ)*X 2 0+(2738804987/5000000000 : ℝ)*X 2 1+(-946228971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320288731/10000000000 : ℝ)*X 0 0+(1158981323/2500000000 : ℝ)*X 0 1+(1006262391/2500000000 : ℝ)*X 0 2+(4320288731/10000000000 : ℝ)*X 1 0+(1158981323/2500000000 : ℝ)*X 1 1+(1006262391/2500000000 : ℝ)*X 1 2+(4320288731/10000000000 : ℝ)*X 2 0+(1158981323/2500000000 : ℝ)*X 2 1+(1006262391/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8160143116653871616777113/930000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62182019/4000000000000 : ℝ)*(base19) + (778455963/50000000000000 : ℝ)*(base23) + (13591657/50000000000000 : ℝ)*(lower2) + (26150887/12500000000000 : ℝ)*(upper3) + (83246097/50000000000000 : ℝ)*(upper5) + (2501683790955551/100000000000000 : ℝ)*(major0) + (2501683790955551/100000000000000 : ℝ)*(major1) + (78177618467361/3125000000000 : ℝ)*(major2) + (211683481724419/6250000000000 : ℝ)*(sp0) + (1693478532343071/50000000000000 : ℝ)*(sp1) + (846739265581173/25000000000000 : ℝ)*(sp2) + (404099564027601/25000000000000 : ℝ)*(sp3) + (11455822957/50000000000000 : ℝ)*(sp4) + (162720091/1562500000000 : ℝ)*(sp7) + (404102167549057/25000000000000 : ℝ)*(f.failure) + (1693479309618309/50000000000000 : ℝ)*(f.sum) + (22631217739171/6277500000000000000000000000 : ℝ)*base66 + (20543520439631765303/2511000000000000000000000000000000 : ℝ)*base68 + (137068173473230267/78468750000000000000000000000000 : ℝ)*base69 + (33392559031787765303/2511000000000000000000000000000000 : ℝ)*base72 + (17318432644883/3138750000000000000000000000 : ℝ)*base74 + (1685015575375105267/78468750000000000000000000000000 : ℝ)*base75 + (451552819745218367/279000000000000000000000000000000 : ℝ)*base78 + (1868250047105218367/279000000000000000000000000000000 : ℝ)*base80 + (7460992860191/1569375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (17525741/1250000000000000000000 : ℝ)*base89 + (17525741/1250000000000000000000 : ℝ)*base91 + (5025741/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8009891672110024475227/1395000000000000000000000000 : ℝ) := by norm_num
    linear_combination (300985917/25000000000000 : ℝ)*(base19) + (689155271/50000000000000 : ℝ)*(base23) + (150355569/100000000000000 : ℝ)*(upper3) + (1291667/2000000000000 : ℝ)*(lower4) + (39789549/50000000000000 : ℝ)*(upper5) + (1266772095631779/50000000000000 : ℝ)*(major0) + (1266772095631779/50000000000000 : ℝ)*(major1) + (1266772095631779/50000000000000 : ℝ)*(major2) + (837387697/6250000000000 : ℝ)*(sp1) + (8222787289/50000000000000 : ℝ)*(sp2) + (214380850935189/6250000000000 : ℝ)*(sp4) + (686015802563241/20000000000000 : ℝ)*(sp5) + (686015158215581/20000000000000 : ℝ)*(sp6) + (818497288084413/50000000000000 : ℝ)*(sp7) + (818497288084413/50000000000000 : ℝ)*(f.failure) + (214380850935189/6250000000000 : ℝ)*(f.sum) + (5450832078559/2092500000000000000000000000 : ℝ)*base66 + (177287474882937919/46500000000000000000000000000000 : ℝ)*base67 + (91453366682937919/46500000000000000000000000000000 : ℝ)*base69 + (64412937136562081/46500000000000000000000000000000 : ℝ)*base72 + (3935370332891/2092500000000000000000000000 : ℝ)*base73 + (360061719435062081/46500000000000000000000000000000 : ℝ)*base76 + (25371346574937919/46500000000000000000000000000000 : ℝ)*base77 + (272044779498062081/46500000000000000000000000000000 : ℝ)*base80 + (14585025529/130781250000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10689369/2500000000000000000000 : ℝ)*base89 + (10689369/2500000000000000000000 : ℝ)*base91 + (10689369/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1343_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9727/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6899/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4929/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (161/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1343_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1343_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4929/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (161/1000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1343_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1343_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1343_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4929/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (161/1000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1343_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
