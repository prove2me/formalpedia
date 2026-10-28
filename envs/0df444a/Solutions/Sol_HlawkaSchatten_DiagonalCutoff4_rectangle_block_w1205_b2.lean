-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1205_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:45.623999+00:00
-- url     : https://prove2.me/submissions/f8a31742-c71c-42ca-873f-dd80af730202

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
theorem support_rectangle_w1205_s6_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068548253/5000000000 : ℝ)*x 0 + (21568509/40000000 : ℝ)*x 1 + (5266471267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068548253/5000000000 : ℝ)^4199 ≤ (12992096125049/100000000000000 : ℝ)^3175 := by
    have hnat : (1068548253 : ℕ)^4199*100000000000000^3175 ≤ 12992096125049^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068548253 5000000000 12992096125049 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21568509/40000000 : ℝ)^4199 ≤ (353457728493/800000000000 : ℝ)^3175 := by
    have hnat : (21568509 : ℕ)^4199*800000000000^3175 ≤ 353457728493^3175*40000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21568509 40000000 353457728493 800000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266471267/10000000000 : ℝ)^4199 ≤ (10706421948491/25000000000000 : ℝ)^3175 := by
    have hnat : (5266471267 : ℕ)^4199*25000000000000^3175 ≤ 10706421948491^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266471267 10000000000 10706421948491 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068548253/5000000000 : ℝ), (21568509/40000000 : ℝ), (5266471267/10000000000 : ℝ)] ![(12992096125049/100000000000000 : ℝ), (353457728493/800000000000 : ℝ), (10706421948491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068548253/5000000000 : ℝ)|^4199 ≤ (12992096125049/100000000000000 : ℝ)^3175
        have hw : |(-1068548253/5000000000 : ℝ)|=(1068548253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21568509/40000000 : ℝ)|^4199 ≤ (353457728493/800000000000 : ℝ)^3175
        have hw : |(21568509/40000000 : ℝ)|=(21568509/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266471267/10000000000 : ℝ)|^4199 ≤ (10706421948491/25000000000000 : ℝ)^3175
        have hw : |(5266471267/10000000000 : ℝ)|=(5266471267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s6_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344555187/10000000000 : ℝ)*x 0 + (-550204853/2500000000 : ℝ)*x 1 + (1053294247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344555187/10000000000 : ℝ)^4199 ≤ (10916858934673/25000000000000 : ℝ)^3175 := by
    have hnat : (5344555187 : ℕ)^4199*25000000000000^3175 ≤ 10916858934673^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344555187 10000000000 10916858934673 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (550204853/2500000000 : ℝ)^4199 ≤ (844179799621/6250000000000 : ℝ)^3175 := by
    have hnat : (550204853 : ℕ)^4199*6250000000000^3175 ≤ 844179799621^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550204853 2500000000 844179799621 6250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053294247/2000000000 : ℝ)^4199 ≤ (42825687449823/100000000000000 : ℝ)^3175 := by
    have hnat : (1053294247 : ℕ)^4199*100000000000000^3175 ≤ 42825687449823^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053294247 2000000000 42825687449823 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344555187/10000000000 : ℝ), (-550204853/2500000000 : ℝ), (1053294247/2000000000 : ℝ)] ![(10916858934673/25000000000000 : ℝ), (844179799621/6250000000000 : ℝ), (42825687449823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344555187/10000000000 : ℝ)|^4199 ≤ (10916858934673/25000000000000 : ℝ)^3175
        have hw : |(5344555187/10000000000 : ℝ)|=(5344555187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-550204853/2500000000 : ℝ)|^4199 ≤ (844179799621/6250000000000 : ℝ)^3175
        have hw : |(-550204853/2500000000 : ℝ)|=(550204853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053294247/2000000000 : ℝ)|^4199 ≤ (42825687449823/100000000000000 : ℝ)^3175
        have hw : |(1053294247/2000000000 : ℝ)|=(1053294247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s6_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133613879/250000000 : ℝ)*x 0 + (5266471243/10000000000 : ℝ)*x 1 + (-1100409719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133613879/250000000 : ℝ)^4199 ≤ (21833717723471/50000000000000 : ℝ)^3175 := by
    have hnat : (133613879 : ℕ)^4199*50000000000000^3175 ≤ 21833717723471^3175*250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133613879 250000000 21833717723471 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266471243/10000000000 : ℝ)^4199 ≤ (21412843767929/50000000000000 : ℝ)^3175 := by
    have hnat : (5266471243 : ℕ)^4199*50000000000000^3175 ≤ 21412843767929^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266471243 10000000000 21412843767929 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1100409719/5000000000 : ℝ)^4199 ≤ (13506877004967/100000000000000 : ℝ)^3175 := by
    have hnat : (1100409719 : ℕ)^4199*100000000000000^3175 ≤ 13506877004967^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100409719 5000000000 13506877004967 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133613879/250000000 : ℝ), (5266471243/10000000000 : ℝ), (-1100409719/5000000000 : ℝ)] ![(21833717723471/50000000000000 : ℝ), (21412843767929/50000000000000 : ℝ), (13506877004967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133613879/250000000 : ℝ)|^4199 ≤ (21833717723471/50000000000000 : ℝ)^3175
        have hw : |(133613879/250000000 : ℝ)|=(133613879/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266471243/10000000000 : ℝ)|^4199 ≤ (21412843767929/50000000000000 : ℝ)^3175
        have hw : |(5266471243/10000000000 : ℝ)|=(5266471243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1100409719/5000000000 : ℝ)|^4199 ≤ (13506877004967/100000000000000 : ℝ)^3175
        have hw : |(-1100409719/5000000000 : ℝ)|=(1100409719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s6_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2177930339/5000000000 : ℝ)*x 0 + (846224407/2000000000 : ℝ)*x 1 + (1121051071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177930339/5000000000 : ℝ)^4199 ≤ (6663435986117/20000000000000 : ℝ)^3175 := by
    have hnat : (2177930339 : ℕ)^4199*20000000000000^3175 ≤ 6663435986117^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177930339 5000000000 6663435986117 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846224407/2000000000 : ℝ)^4199 ≤ (32061225128727/100000000000000 : ℝ)^3175 := by
    have hnat : (846224407 : ℕ)^4199*100000000000000^3175 ≤ 32061225128727^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846224407 2000000000 32061225128727 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121051071/2500000000 : ℝ)^4199 ≤ (4327699364607/12500000000000 : ℝ)^3175 := by
    have hnat : (1121051071 : ℕ)^4199*12500000000000^3175 ≤ 4327699364607^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121051071 2500000000 4327699364607 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177930339/5000000000 : ℝ), (846224407/2000000000 : ℝ), (1121051071/2500000000 : ℝ)] ![(6663435986117/20000000000000 : ℝ), (32061225128727/100000000000000 : ℝ), (4327699364607/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177930339/5000000000 : ℝ)|^4199 ≤ (6663435986117/20000000000000 : ℝ)^3175
        have hw : |(2177930339/5000000000 : ℝ)|=(2177930339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846224407/2000000000 : ℝ)|^4199 ≤ (32061225128727/100000000000000 : ℝ)^3175
        have hw : |(846224407/2000000000 : ℝ)|=(846224407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121051071/2500000000 : ℝ)|^4199 ≤ (4327699364607/12500000000000 : ℝ)^3175
        have hw : |(1121051071/2500000000 : ℝ)|=(1121051071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s6_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137101323/10000000000 : ℝ)*x 0 + (1053357777/2000000000 : ℝ)*x 1 + (5391808459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137101323/10000000000 : ℝ)^4199 ≤ (12992134853849/100000000000000 : ℝ)^3175 := by
    have hnat : (2137101323 : ℕ)^4199*100000000000000^3175 ≤ 12992134853849^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137101323 10000000000 12992134853849 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053357777/2000000000 : ℝ)^4199 ≤ (42829103622819/100000000000000 : ℝ)^3175 := by
    have hnat : (1053357777 : ℕ)^4199*100000000000000^3175 ≤ 42829103622819^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053357777 2000000000 42829103622819 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391808459/10000000000 : ℝ)^4199 ≤ (22089380756067/50000000000000 : ℝ)^3175 := by
    have hnat : (5391808459 : ℕ)^4199*50000000000000^3175 ≤ 22089380756067^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391808459 10000000000 22089380756067 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137101323/10000000000 : ℝ), (1053357777/2000000000 : ℝ), (5391808459/10000000000 : ℝ)] ![(12992134853849/100000000000000 : ℝ), (42829103622819/100000000000000 : ℝ), (22089380756067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137101323/10000000000 : ℝ)|^4199 ≤ (12992134853849/100000000000000 : ℝ)^3175
        have hw : |(-2137101323/10000000000 : ℝ)|=(2137101323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053357777/2000000000 : ℝ)|^4199 ≤ (42829103622819/100000000000000 : ℝ)^3175
        have hw : |(1053357777/2000000000 : ℝ)|=(1053357777/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391808459/10000000000 : ℝ)|^4199 ≤ (22089380756067/50000000000000 : ℝ)^3175
        have hw : |(5391808459/10000000000 : ℝ)|=(5391808459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s6_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062514983/2000000000 : ℝ)*x 0 + (-2075482189/10000000000 : ℝ)*x 1 + (2695904247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062514983/2000000000 : ℝ)^4199 ≤ (2707637756393/6250000000000 : ℝ)^3175 := by
    have hnat : (1062514983 : ℕ)^4199*6250000000000^3175 ≤ 2707637756393^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062514983 2000000000 2707637756393 6250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2075482189/10000000000 : ℝ)^4199 ≤ (6249516996893/50000000000000 : ℝ)^3175 := by
    have hnat : (2075482189 : ℕ)^4199*50000000000000^3175 ≤ 6249516996893^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2075482189 10000000000 6249516996893 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695904247/5000000000 : ℝ)^4199 ≤ (8835752378281/20000000000000 : ℝ)^3175 := by
    have hnat : (2695904247 : ℕ)^4199*20000000000000^3175 ≤ 8835752378281^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695904247 5000000000 8835752378281 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062514983/2000000000 : ℝ), (-2075482189/10000000000 : ℝ), (2695904247/5000000000 : ℝ)] ![(2707637756393/6250000000000 : ℝ), (6249516996893/50000000000000 : ℝ), (8835752378281/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062514983/2000000000 : ℝ)|^4199 ≤ (2707637756393/6250000000000 : ℝ)^3175
        have hw : |(1062514983/2000000000 : ℝ)|=(1062514983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2075482189/10000000000 : ℝ)|^4199 ≤ (6249516996893/50000000000000 : ℝ)^3175
        have hw : |(-2075482189/10000000000 : ℝ)|=(2075482189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695904247/5000000000 : ℝ)|^4199 ≤ (8835752378281/20000000000000 : ℝ)^3175
        have hw : |(2695904247/5000000000 : ℝ)|=(2695904247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s6_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (332035931/625000000 : ℝ)*x 0 + (5265438/9765625 : ℝ)*x 1 + (-207548219/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332035931/625000000 : ℝ)^4199 ≤ (43322203897379/100000000000000 : ℝ)^3175 := by
    have hnat : (332035931 : ℕ)^4199*100000000000000^3175 ≤ 43322203897379^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332035931 625000000 43322203897379 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265438/9765625 : ℝ)^4199 ≤ (22089381043229/50000000000000 : ℝ)^3175 := by
    have hnat : (5265438 : ℕ)^4199*50000000000000^3175 ≤ 22089381043229^3175*9765625^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265438 9765625 22089381043229 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207548219/1000000000 : ℝ)^4199 ≤ (12499034001751/100000000000000 : ℝ)^3175 := by
    have hnat : (207548219 : ℕ)^4199*100000000000000^3175 ≤ 12499034001751^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207548219 1000000000 12499034001751 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332035931/625000000 : ℝ), (5265438/9765625 : ℝ), (-207548219/1000000000 : ℝ)] ![(43322203897379/100000000000000 : ℝ), (22089381043229/50000000000000 : ℝ), (12499034001751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332035931/625000000 : ℝ)|^4199 ≤ (43322203897379/100000000000000 : ℝ)^3175
        have hw : |(332035931/625000000 : ℝ)|=(332035931/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265438/9765625 : ℝ)|^4199 ≤ (22089381043229/50000000000000 : ℝ)^3175
        have hw : |(5265438/9765625 : ℝ)|=(5265438/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-207548219/1000000000 : ℝ)|^4199 ≤ (12499034001751/100000000000000 : ℝ)^3175
        have hw : |(-207548219/1000000000 : ℝ)|=(207548219/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s6_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435587041/1000000000 : ℝ)*x 0 + (4483564513/10000000000 : ℝ)*x 1 + (4231764053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435587041/1000000000 : ℝ)^4199 ≤ (8329319594179/25000000000000 : ℝ)^3175 := by
    have hnat : (435587041 : ℕ)^4199*25000000000000^3175 ≤ 8329319594179^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435587041 1000000000 8329319594179 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483564513/10000000000 : ℝ)^4199 ≤ (34615062432411/100000000000000 : ℝ)^3175 := by
    have hnat : (4483564513 : ℕ)^4199*100000000000000^3175 ≤ 34615062432411^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483564513 10000000000 34615062432411 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231764053/10000000000 : ℝ)^4199 ≤ (32067659180301/100000000000000 : ℝ)^3175 := by
    have hnat : (4231764053 : ℕ)^4199*100000000000000^3175 ≤ 32067659180301^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231764053 10000000000 32067659180301 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435587041/1000000000 : ℝ), (4483564513/10000000000 : ℝ), (4231764053/10000000000 : ℝ)] ![(8329319594179/25000000000000 : ℝ), (34615062432411/100000000000000 : ℝ), (32067659180301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435587041/1000000000 : ℝ)|^4199 ≤ (8329319594179/25000000000000 : ℝ)^3175
        have hw : |(435587041/1000000000 : ℝ)|=(435587041/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483564513/10000000000 : ℝ)|^4199 ≤ (34615062432411/100000000000000 : ℝ)^3175
        have hw : |(4483564513/10000000000 : ℝ)|=(4483564513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231764053/10000000000 : ℝ)|^4199 ≤ (32067659180301/100000000000000 : ℝ)^3175
        have hw : |(4231764053/10000000000 : ℝ)|=(4231764053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2857/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2851/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2823/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2851/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2823/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2851/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2851/25000 : ℝ) ^ (8397/2048 : ℝ) ≤ (1701188679931719/12500000000000000000 : ℝ) := by
    have hpowers : (2851/25000 : ℝ)^8397 ≤ (1701188679931719/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2851 : ℕ)^8397*12500000000000000000^2048 ≤ 1701188679931719^2048*25000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2851 25000 1701188679931719 12500000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2851/25000 : ℝ)) (X := (1701188679931719/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2823/20000 : ℝ) ^ (8397/2048 : ℝ) ≤ (32629361779664263/100000000000000000000 : ℝ) := by
    have hpowers : (2823/20000 : ℝ)^8397 ≤ (32629361779664263/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2823 : ℕ)^8397*100000000000000000000^2048 ≤ 32629361779664263^2048*20000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2823 20000 32629361779664263 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2823/20000 : ℝ)) (X := (32629361779664263/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251701188679931719/6250000000000000000 : ℝ) ≤ (5000331897197537/5000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (6251701188679931719/6250000000000000000 : ℝ)^2048 ≤ (5000331897197537/5000000000000000 : ℝ)^8397 := by
      have hnat : (6251701188679931719 : ℕ)^2048*5000000000000000^8397 ≤ 5000331897197537^8397*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251701188679931719 6250000000000000000 5000331897197537 5000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000331897197537/5000000000000000 : ℝ)) (X := (6251701188679931719/6250000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009247774243823603/20000000000000000000 : ℝ) ≤ (5000563776700113/5000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (20009247774243823603/20000000000000000000 : ℝ)^2048 ≤ (5000563776700113/5000000000000000 : ℝ)^8397 := by
      have hnat : (20009247774243823603 : ℕ)^2048*5000000000000000^8397 ≤ 5000563776700113^8397*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009247774243823603 20000000000000000000 5000563776700113 5000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000563776700113/5000000000000000 : ℝ)) (X := (20009247774243823603/20000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032629361779664263/50000000000000000000 : ℝ) ≤ (5000795656202689/5000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50032629361779664263/50000000000000000000 : ℝ)^2048 ≤ (5000795656202689/5000000000000000 : ℝ)^8397 := by
      have hnat : (50032629361779664263 : ℕ)^2048*5000000000000000^8397 ≤ 5000795656202689^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032629361779664263 50000000000000000000 5000795656202689 5000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000795656202689/5000000000000000 : ℝ)) (X := (50032629361779664263/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1701188679931719/12500000000000000000 : ℝ) ≤ ((13550611065607769399/13555000000000000000 : ℝ)+2*(14492468911/8471875000000 : ℝ)*(2851/25000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (13550611065607769399/13555000000000000000 : ℝ)+2*(14492468911/8471875000000 : ℝ)*(2851/25000 : ℝ)=(5000331897197537/5000000000000000 : ℝ) by norm_num, show 1+2*(1701188679931719/12500000000000000000 : ℝ)=(6251701188679931719/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32629361779664263/100000000000000000000 : ℝ)+(1701188679931719/12500000000000000000 : ℝ) ≤ ((13550611065607769399/13555000000000000000 : ℝ)+(14492468911/8471875000000 : ℝ)*((2823/20000 : ℝ)+(2851/25000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (13550611065607769399/13555000000000000000 : ℝ)+(14492468911/8471875000000 : ℝ)*((2823/20000 : ℝ)+(2851/25000 : ℝ))=(5000563776700113/5000000000000000 : ℝ) by norm_num, show 1+(32629361779664263/100000000000000000000 : ℝ)+(1701188679931719/12500000000000000000 : ℝ)=(20009247774243823603/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32629361779664263/100000000000000000000 : ℝ) ≤ ((13550611065607769399/13555000000000000000 : ℝ)+2*(14492468911/8471875000000 : ℝ)*(2823/20000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (13550611065607769399/13555000000000000000 : ℝ)+2*(14492468911/8471875000000 : ℝ)*(2823/20000 : ℝ)=(5000795656202689/5000000000000000 : ℝ) by norm_num, show 1+2*(32629361779664263/100000000000000000000 : ℝ)=(50032629361779664263/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13550611065607769399/13555000000000000000 : ℝ)*(X 1 0+X 2 0)+(14492468911/8471875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (13550611065607769399/13555000000000000000 : ℝ)) (alpha := (14492468911/8471875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13550611065607769399/13555000000000000000 : ℝ)*(X 0 1+X 2 1)+(14492468911/8471875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (13550611065607769399/13555000000000000000 : ℝ)) (alpha := (14492468911/8471875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13550611065607769399/13555000000000000000 : ℝ)*(X 0 2+X 1 2)+(14492468911/8471875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (2851/25000 : ℝ)) (hi := (2823/20000 : ℝ)) (c := (13550611065607769399/13555000000000000000 : ℝ)) (alpha := (14492468911/8471875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1068548253/5000000000 : ℝ)*X 0 0+(21568509/40000000 : ℝ)*X 0 1+(5266471267/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344555187/10000000000 : ℝ)*X 1 0+(-550204853/2500000000 : ℝ)*X 1 1+(1053294247/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133613879/250000000 : ℝ)*X 2 0+(5266471243/10000000000 : ℝ)*X 2 1+(-1100409719/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177930339/5000000000 : ℝ)*X 0 0+(846224407/2000000000 : ℝ)*X 0 1+(1121051071/2500000000 : ℝ)*X 0 2+(2177930339/5000000000 : ℝ)*X 1 0+(846224407/2000000000 : ℝ)*X 1 1+(1121051071/2500000000 : ℝ)*X 1 2+(2177930339/5000000000 : ℝ)*X 2 0+(846224407/2000000000 : ℝ)*X 2 1+(1121051071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2137101323/10000000000 : ℝ)*X 0 0+(1053357777/2000000000 : ℝ)*X 0 1+(5391808459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062514983/2000000000 : ℝ)*X 1 0+(-2075482189/10000000000 : ℝ)*X 1 1+(2695904247/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332035931/625000000 : ℝ)*X 2 0+(5265438/9765625 : ℝ)*X 2 1+(-207548219/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435587041/1000000000 : ℝ)*X 0 0+(4483564513/10000000000 : ℝ)*X 0 1+(4231764053/10000000000 : ℝ)*X 0 2+(435587041/1000000000 : ℝ)*X 1 0+(4483564513/10000000000 : ℝ)*X 1 1+(4231764053/10000000000 : ℝ)*X 1 2+(435587041/1000000000 : ℝ)*X 2 0+(4483564513/10000000000 : ℝ)*X 2 1+(4231764053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17125402208061683699214501/2117968750000000000000000000000 : ℝ) := by norm_num
    linear_combination (6063139/400000000000 : ℝ)*(base19) + (1378252441/100000000000000 : ℝ)*(base23) + (52017443/100000000000000 : ℝ)*(lower2) + (202748799/100000000000000 : ℝ)*(upper3) + (81933063/100000000000000 : ℝ)*(upper5) + (74435289169691/1250000000000 : ℝ)*(major0) + (74435289169691/1250000000000 : ℝ)*(major1) + (74435289169691/1250000000000 : ℝ)*(major2) + (3979140019414131/50000000000000 : ℝ)*(sp0) + (3979158780295217/50000000000000 : ℝ)*(sp1) + (994789712265343/12500000000000 : ℝ)*(sp2) + (987826084287513/25000000000000 : ℝ)*(sp3) + (19518773461/50000000000000 : ℝ)*(sp4) + (22584099741/100000000000000 : ℝ)*(sp7) + (3858717696533/97656250000 : ℝ)*(f.failure) + (497394942273449/6250000000000 : ℝ)*(f.sum) + (1700348585291/169437500000000000000000000 : ℝ)*base66 + (19554311507520541/16943750000000000000000000000000 : ℝ)*base68 + (156314193022958041/16943750000000000000000000000000 : ℝ)*base70 + (47593569789285709/16943750000000000000000000000000 : ℝ)*base71 + (115898373417/2711000000000000000000000000 : ℝ)*base73 + (181011484996820541/16943750000000000000000000000000 : ℝ)*base76 + (171680207323851791/16943750000000000000000000000000 : ℝ)*base78 + (194148630332158041/16943750000000000000000000000000 : ℝ)*base80 + (22018204874647/2711000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5763/976562500000000000 : ℝ)*base90 + (5763/976562500000000000 : ℝ)*base92 + (5763/976562500000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2222429353401909221812873683/338875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1138149081/100000000000000 : ℝ)*(base19) + (307438943/25000000000000 : ℝ)*(base23) + (146479951/100000000000000 : ℝ)*(upper3) + (53073969/100000000000000 : ℝ)*(lower4) + (128074423/100000000000000 : ℝ)*(upper5) + (5985071729132039/100000000000000 : ℝ)*(major0) + (5985071729132039/100000000000000 : ℝ)*(major1) + (5985071729132039/100000000000000 : ℝ)*(major2) + (8098081773/25000000000000 : ℝ)*(sp1) + (35766411833/100000000000000 : ℝ)*(sp2) + (1599748968469601/20000000000000 : ℝ)*(sp4) + (7998711311871833/100000000000000 : ℝ)*(sp5) + (19996769615451/250000000000 : ℝ)*(sp6) + (496424799663437/12500000000000 : ℝ)*(sp7) + (496424799663437/12500000000000 : ℝ)*(f.failure) + (1599748968469601/20000000000000 : ℝ)*(f.sum) + (116499159656453/13555000000000000000000000000 : ℝ)*base65 + (16472007786470425439/1355500000000000000000000000000000 : ℝ)*base68 + (4964086204375425439/1355500000000000000000000000000000 : ℝ)*base70 + (6945915355556574561/1355500000000000000000000000000000 : ℝ)*base71 + (879202020457/13555000000000000000000000000 : ℝ)*base74 + (7888135326873925439/1355500000000000000000000000000000 : ℝ)*base76 + (5297436805838925439/1355500000000000000000000000000000 : ℝ)*base78 + (4490822981737425439/1355500000000000000000000000000000 : ℝ)*base80 + (13058072678529/6777500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (911157/125000000000000000000 : ℝ)*base90 + (911157/125000000000000000000 : ℝ)*base92 + (911157/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1205_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1205_s7_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213711653/1000000000 : ℝ)*x 0 + (336993121/625000000 : ℝ)*x 1 + (263334771/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213711653/1000000000 : ℝ)^4199 ≤ (3248064279673/25000000000000 : ℝ)^3175 := by
    have hnat : (213711653 : ℕ)^4199*25000000000000^3175 ≤ 3248064279673^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213711653 1000000000 3248064279673 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336993121/625000000 : ℝ)^4199 ≤ (552245555299/1250000000000 : ℝ)^3175 := by
    have hnat : (336993121 : ℕ)^4199*1250000000000^3175 ≤ 552245555299^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336993121 625000000 552245555299 1250000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263334771/500000000 : ℝ)^4199 ≤ (42828098444791/100000000000000 : ℝ)^3175 := by
    have hnat : (263334771 : ℕ)^4199*100000000000000^3175 ≤ 42828098444791^3175*500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263334771 500000000 42828098444791 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213711653/1000000000 : ℝ), (336993121/625000000 : ℝ), (263334771/500000000 : ℝ)] ![(3248064279673/25000000000000 : ℝ), (552245555299/1250000000000 : ℝ), (42828098444791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213711653/1000000000 : ℝ)|^4199 ≤ (3248064279673/25000000000000 : ℝ)^3175
        have hw : |(-213711653/1000000000 : ℝ)|=(213711653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336993121/625000000 : ℝ)|^4199 ≤ (552245555299/1250000000000 : ℝ)^3175
        have hw : |(336993121/625000000 : ℝ)|=(336993121/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263334771/500000000 : ℝ)|^4199 ≤ (42828098444791/100000000000000 : ℝ)^3175
        have hw : |(263334771/500000000 : ℝ)|=(263334771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s7_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213779811/400000000 : ℝ)*x 0 + (-2200602123/10000000000 : ℝ)*x 1 + (263334771/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213779811/400000000 : ℝ)^4199 ≤ (43666788355677/100000000000000 : ℝ)^3175 := by
    have hnat : (213779811 : ℕ)^4199*100000000000000^3175 ≤ 43666788355677^3175*400000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213779811 400000000 43666788355677 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200602123/10000000000 : ℝ)^4199 ≤ (6752556590041/50000000000000 : ℝ)^3175 := by
    have hnat : (2200602123 : ℕ)^4199*50000000000000^3175 ≤ 6752556590041^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200602123 10000000000 6752556590041 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263334771/500000000 : ℝ)^4199 ≤ (42828098444791/100000000000000 : ℝ)^3175 := by
    have hnat : (263334771 : ℕ)^4199*100000000000000^3175 ≤ 42828098444791^3175*500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263334771 500000000 42828098444791 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213779811/400000000 : ℝ), (-2200602123/10000000000 : ℝ), (263334771/500000000 : ℝ)] ![(43666788355677/100000000000000 : ℝ), (6752556590041/50000000000000 : ℝ), (42828098444791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213779811/400000000 : ℝ)|^4199 ≤ (43666788355677/100000000000000 : ℝ)^3175
        have hw : |(213779811/400000000 : ℝ)|=(213779811/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200602123/10000000000 : ℝ)|^4199 ≤ (6752556590041/50000000000000 : ℝ)^3175
        have hw : |(-2200602123/10000000000 : ℝ)|=(2200602123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(263334771/500000000 : ℝ)|^4199 ≤ (42828098444791/100000000000000 : ℝ)^3175
        have hw : |(263334771/500000000 : ℝ)|=(263334771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s7_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213779811/400000000 : ℝ)*x 0 + (263334771/500000000 : ℝ)*x 1 + (-2200602123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213779811/400000000 : ℝ)^4199 ≤ (43666788355677/100000000000000 : ℝ)^3175 := by
    have hnat : (213779811 : ℕ)^4199*100000000000000^3175 ≤ 43666788355677^3175*400000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213779811 400000000 43666788355677 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263334771/500000000 : ℝ)^4199 ≤ (42828098444791/100000000000000 : ℝ)^3175 := by
    have hnat : (263334771 : ℕ)^4199*100000000000000^3175 ≤ 42828098444791^3175*500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263334771 500000000 42828098444791 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200602123/10000000000 : ℝ)^4199 ≤ (6752556590041/50000000000000 : ℝ)^3175 := by
    have hnat : (2200602123 : ℕ)^4199*50000000000000^3175 ≤ 6752556590041^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200602123 10000000000 6752556590041 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213779811/400000000 : ℝ), (263334771/500000000 : ℝ), (-2200602123/10000000000 : ℝ)] ![(43666788355677/100000000000000 : ℝ), (42828098444791/100000000000000 : ℝ), (6752556590041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213779811/400000000 : ℝ)|^4199 ≤ (43666788355677/100000000000000 : ℝ)^3175
        have hw : |(213779811/400000000 : ℝ)|=(213779811/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263334771/500000000 : ℝ)|^4199 ≤ (42828098444791/100000000000000 : ℝ)^3175
        have hw : |(263334771/500000000 : ℝ)|=(263334771/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2200602123/10000000000 : ℝ)|^4199 ≤ (6752556590041/50000000000000 : ℝ)^3175
        have hw : |(-2200602123/10000000000 : ℝ)|=(2200602123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s7_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355872439/10000000000 : ℝ)*x 0 + (1057896313/2500000000 : ℝ)*x 1 + (2241868999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355872439/10000000000 : ℝ)^4199 ≤ (33317298901509/100000000000000 : ℝ)^3175 := by
    have hnat : (4355872439 : ℕ)^4199*100000000000000^3175 ≤ 33317298901509^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355872439 10000000000 33317298901509 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057896313/2500000000 : ℝ)^4199 ≤ (32065867275457/100000000000000 : ℝ)^3175 := by
    have hnat : (1057896313 : ℕ)^4199*100000000000000^3175 ≤ 32065867275457^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057896313 2500000000 32065867275457 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241868999/5000000000 : ℝ)^4199 ≤ (34616833799133/100000000000000 : ℝ)^3175 := by
    have hnat : (2241868999 : ℕ)^4199*100000000000000^3175 ≤ 34616833799133^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241868999 5000000000 34616833799133 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355872439/10000000000 : ℝ), (1057896313/2500000000 : ℝ), (2241868999/5000000000 : ℝ)] ![(33317298901509/100000000000000 : ℝ), (32065867275457/100000000000000 : ℝ), (34616833799133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355872439/10000000000 : ℝ)|^4199 ≤ (33317298901509/100000000000000 : ℝ)^3175
        have hw : |(4355872439/10000000000 : ℝ)|=(4355872439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057896313/2500000000 : ℝ)|^4199 ≤ (32065867275457/100000000000000 : ℝ)^3175
        have hw : |(1057896313/2500000000 : ℝ)|=(1057896313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241868999/5000000000 : ℝ)|^4199 ≤ (34616833799133/100000000000000 : ℝ)^3175
        have hw : |(2241868999/5000000000 : ℝ)|=(2241868999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s7_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-213712127/1000000000 : ℝ)*x 0 + (2633505359/5000000000 : ℝ)*x 1 + (1078314699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213712127/1000000000 : ℝ)^4199 ≤ (519691809141/4000000000000 : ℝ)^3175 := by
    have hnat : (213712127 : ℕ)^4199*4000000000000^3175 ≤ 519691809141^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213712127 1000000000 519691809141 4000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633505359/5000000000 : ℝ)^4199 ≤ (21415744684733/50000000000000 : ℝ)^3175 := by
    have hnat : (2633505359 : ℕ)^4199*50000000000000^3175 ≤ 21415744684733^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633505359 5000000000 21415744684733 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078314699/2000000000 : ℝ)^4199 ≤ (5522026923553/12500000000000 : ℝ)^3175 := by
    have hnat : (1078314699 : ℕ)^4199*12500000000000^3175 ≤ 5522026923553^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078314699 2000000000 5522026923553 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-213712127/1000000000 : ℝ), (2633505359/5000000000 : ℝ), (1078314699/2000000000 : ℝ)] ![(519691809141/4000000000000 : ℝ), (21415744684733/50000000000000 : ℝ), (5522026923553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-213712127/1000000000 : ℝ)|^4199 ≤ (519691809141/4000000000000 : ℝ)^3175
        have hw : |(-213712127/1000000000 : ℝ)|=(213712127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633505359/5000000000 : ℝ)|^4199 ≤ (21415744684733/50000000000000 : ℝ)^3175
        have hw : |(2633505359/5000000000 : ℝ)|=(2633505359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078314699/2000000000 : ℝ)|^4199 ≤ (5522026923553/12500000000000 : ℝ)^3175
        have hw : |(1078314699/2000000000 : ℝ)|=(1078314699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s7_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312632419/10000000000 : ℝ)*x 0 + (-129732753/625000000 : ℝ)*x 1 + (1078314699/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312632419/10000000000 : ℝ)^4199 ≤ (43322824266121/100000000000000 : ℝ)^3175 := by
    have hnat : (5312632419 : ℕ)^4199*100000000000000^3175 ≤ 43322824266121^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312632419 10000000000 43322824266121 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129732753/625000000 : ℝ)^4199 ≤ (12500960320721/100000000000000 : ℝ)^3175 := by
    have hnat : (129732753 : ℕ)^4199*100000000000000^3175 ≤ 12500960320721^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129732753 625000000 12500960320721 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078314699/2000000000 : ℝ)^4199 ≤ (5522026923553/12500000000000 : ℝ)^3175 := by
    have hnat : (1078314699 : ℕ)^4199*12500000000000^3175 ≤ 5522026923553^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078314699 2000000000 5522026923553 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312632419/10000000000 : ℝ), (-129732753/625000000 : ℝ), (1078314699/2000000000 : ℝ)] ![(43322824266121/100000000000000 : ℝ), (12500960320721/100000000000000 : ℝ), (5522026923553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312632419/10000000000 : ℝ)|^4199 ≤ (43322824266121/100000000000000 : ℝ)^3175
        have hw : |(5312632419/10000000000 : ℝ)|=(5312632419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-129732753/625000000 : ℝ)|^4199 ≤ (12500960320721/100000000000000 : ℝ)^3175
        have hw : |(-129732753/625000000 : ℝ)|=(129732753/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078314699/2000000000 : ℝ)|^4199 ≤ (5522026923553/12500000000000 : ℝ)^3175
        have hw : |(1078314699/2000000000 : ℝ)|=(1078314699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s7_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312632419/10000000000 : ℝ)*x 0 + (1078314699/2000000000 : ℝ)*x 1 + (-129732753/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312632419/10000000000 : ℝ)^4199 ≤ (43322824266121/100000000000000 : ℝ)^3175 := by
    have hnat : (5312632419 : ℕ)^4199*100000000000000^3175 ≤ 43322824266121^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312632419 10000000000 43322824266121 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078314699/2000000000 : ℝ)^4199 ≤ (5522026923553/12500000000000 : ℝ)^3175 := by
    have hnat : (1078314699 : ℕ)^4199*12500000000000^3175 ≤ 5522026923553^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078314699 2000000000 5522026923553 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129732753/625000000 : ℝ)^4199 ≤ (12500960320721/100000000000000 : ℝ)^3175 := by
    have hnat : (129732753 : ℕ)^4199*100000000000000^3175 ≤ 12500960320721^3175*625000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129732753 625000000 12500960320721 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312632419/10000000000 : ℝ), (1078314699/2000000000 : ℝ), (-129732753/625000000 : ℝ)] ![(43322824266121/100000000000000 : ℝ), (5522026923553/12500000000000 : ℝ), (12500960320721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312632419/10000000000 : ℝ)|^4199 ≤ (43322824266121/100000000000000 : ℝ)^3175
        have hw : |(5312632419/10000000000 : ℝ)|=(5312632419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078314699/2000000000 : ℝ)|^4199 ≤ (5522026923553/12500000000000 : ℝ)^3175
        have hw : |(1078314699/2000000000 : ℝ)|=(1078314699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-129732753/625000000 : ℝ)|^4199 ≤ (12500960320721/100000000000000 : ℝ)^3175
        have hw : |(-129732753/625000000 : ℝ)|=(129732753/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s7_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (871176397/2000000000 : ℝ)*x 0 + (4483102961/10000000000 : ℝ)*x 1 + (423222259/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871176397/2000000000 : ℝ)^4199 ≤ (16658697733101/50000000000000 : ℝ)^3175 := by
    have hnat : (871176397 : ℕ)^4199*50000000000000^3175 ≤ 16658697733101^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871176397 2000000000 16658697733101 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4483102961/10000000000 : ℝ)^4199 ≤ (8652587467083/25000000000000 : ℝ)^3175 := by
    have hnat : (4483102961 : ℕ)^4199*25000000000000^3175 ≤ 8652587467083^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483102961 10000000000 8652587467083 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423222259/1000000000 : ℝ)^4199 ≤ (16036127325137/50000000000000 : ℝ)^3175 := by
    have hnat : (423222259 : ℕ)^4199*50000000000000^3175 ≤ 16036127325137^3175*1000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423222259 1000000000 16036127325137 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871176397/2000000000 : ℝ), (4483102961/10000000000 : ℝ), (423222259/1000000000 : ℝ)] ![(16658697733101/50000000000000 : ℝ), (8652587467083/25000000000000 : ℝ), (16036127325137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871176397/2000000000 : ℝ)|^4199 ≤ (16658697733101/50000000000000 : ℝ)^3175
        have hw : |(871176397/2000000000 : ℝ)|=(871176397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4483102961/10000000000 : ℝ)|^4199 ≤ (8652587467083/25000000000000 : ℝ)^3175
        have hw : |(4483102961/10000000000 : ℝ)|=(4483102961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423222259/1000000000 : ℝ)|^4199 ≤ (16036127325137/50000000000000 : ℝ)^3175
        have hw : |(423222259/1000000000 : ℝ)|=(423222259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11433/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2817/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2857/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2857/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2857/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1409/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2857/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2857/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1409/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2857/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2857/25000 : ℝ) ^ (8397/2048 : ℝ) ≤ (13727326233267441/100000000000000000000 : ℝ) := by
    have hpowers : (2857/25000 : ℝ)^8397 ≤ (13727326233267441/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2857 : ℕ)^8397*100000000000000000000^2048 ≤ 13727326233267441^2048*25000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2857 25000 13727326233267441 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2857/25000 : ℝ)) (X := (13727326233267441/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1409/10000 : ℝ) ^ (8397/2048 : ℝ) ≤ (32393058668673577/100000000000000000000 : ℝ) := by
    have hpowers : (1409/10000 : ℝ)^8397 ≤ (32393058668673577/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1409 : ℕ)^8397*100000000000000000000^2048 ≤ 32393058668673577^2048*10000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1409 10000 32393058668673577 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1409/10000 : ℝ)) (X := (32393058668673577/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013727326233267441/50000000000000000000 : ℝ) ≤ (10000669540231267/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50013727326233267441/50000000000000000000 : ℝ)^2048 ≤ (10000669540231267/10000000000000000 : ℝ)^8397 := by
      have hnat : (50013727326233267441 : ℕ)^2048*10000000000000000^8397 ≤ 10000669540231267^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013727326233267441 50000000000000000000 10000669540231267 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000669540231267/10000000000000000 : ℝ)) (X := (50013727326233267441/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023060192450970509/50000000000000000000 : ℝ) ≤ (10001124664567507/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50023060192450970509/50000000000000000000 : ℝ)^2048 ≤ (10001124664567507/10000000000000000 : ℝ)^8397 := by
      have hnat : (50023060192450970509 : ℕ)^2048*10000000000000000^8397 ≤ 10001124664567507^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023060192450970509 50000000000000000000 10001124664567507 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001124664567507/10000000000000000 : ℝ)) (X := (50023060192450970509/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032393058668673577/50000000000000000000 : ℝ) ≤ (10001579788903747/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50032393058668673577/50000000000000000000 : ℝ)^2048 ≤ (10001579788903747/10000000000000000 : ℝ)^8397 := by
      have hnat : (50032393058668673577 : ℕ)^2048*10000000000000000^8397 ≤ 10001579788903747^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032393058668673577 50000000000000000000 10001579788903747 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001579788903747/10000000000000000 : ℝ)) (X := (50032393058668673577/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13727326233267441/100000000000000000000 : ℝ) ≤ ((13305689997133265657/13310000000000000000 : ℝ)+2*(5689054203/3327500000000 : ℝ)*(2857/25000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (13305689997133265657/13310000000000000000 : ℝ)+2*(5689054203/3327500000000 : ℝ)*(2857/25000 : ℝ)=(10000669540231267/10000000000000000 : ℝ) by norm_num, show 1+2*(13727326233267441/100000000000000000000 : ℝ)=(50013727326233267441/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32393058668673577/100000000000000000000 : ℝ)+(13727326233267441/100000000000000000000 : ℝ) ≤ ((13305689997133265657/13310000000000000000 : ℝ)+(5689054203/3327500000000 : ℝ)*((1409/10000 : ℝ)+(2857/25000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (13305689997133265657/13310000000000000000 : ℝ)+(5689054203/3327500000000 : ℝ)*((1409/10000 : ℝ)+(2857/25000 : ℝ))=(10001124664567507/10000000000000000 : ℝ) by norm_num, show 1+(32393058668673577/100000000000000000000 : ℝ)+(13727326233267441/100000000000000000000 : ℝ)=(50023060192450970509/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32393058668673577/100000000000000000000 : ℝ) ≤ ((13305689997133265657/13310000000000000000 : ℝ)+2*(5689054203/3327500000000 : ℝ)*(1409/10000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (13305689997133265657/13310000000000000000 : ℝ)+2*(5689054203/3327500000000 : ℝ)*(1409/10000 : ℝ)=(10001579788903747/10000000000000000 : ℝ) by norm_num, show 1+2*(32393058668673577/100000000000000000000 : ℝ)=(50032393058668673577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13305689997133265657/13310000000000000000 : ℝ)*(X 1 0+X 2 0)+(5689054203/3327500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (2857/25000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (13305689997133265657/13310000000000000000 : ℝ)) (alpha := (5689054203/3327500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13305689997133265657/13310000000000000000 : ℝ)*(X 0 1+X 2 1)+(5689054203/3327500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (2857/25000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (13305689997133265657/13310000000000000000 : ℝ)) (alpha := (5689054203/3327500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13305689997133265657/13310000000000000000 : ℝ)*(X 0 2+X 1 2)+(5689054203/3327500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (2857/25000 : ℝ)) (hi := (1409/10000 : ℝ)) (c := (13305689997133265657/13310000000000000000 : ℝ)) (alpha := (5689054203/3327500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-213711653/1000000000 : ℝ)*X 0 0+(336993121/625000000 : ℝ)*X 0 1+(263334771/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213779811/400000000 : ℝ)*X 1 0+(-2200602123/10000000000 : ℝ)*X 1 1+(263334771/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213779811/400000000 : ℝ)*X 2 0+(263334771/500000000 : ℝ)*X 2 1+(-2200602123/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355872439/10000000000 : ℝ)*X 0 0+(1057896313/2500000000 : ℝ)*X 0 1+(2241868999/5000000000 : ℝ)*X 0 2+(4355872439/10000000000 : ℝ)*X 1 0+(1057896313/2500000000 : ℝ)*X 1 1+(2241868999/5000000000 : ℝ)*X 1 2+(4355872439/10000000000 : ℝ)*X 2 0+(1057896313/2500000000 : ℝ)*X 2 1+(2241868999/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-213712127/1000000000 : ℝ)*X 0 0+(2633505359/5000000000 : ℝ)*X 0 1+(1078314699/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312632419/10000000000 : ℝ)*X 1 0+(-129732753/625000000 : ℝ)*X 1 1+(1078314699/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312632419/10000000000 : ℝ)*X 2 0+(1078314699/2000000000 : ℝ)*X 2 1+(-129732753/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((871176397/2000000000 : ℝ)*X 0 0+(4483102961/10000000000 : ℝ)*X 0 1+(423222259/1000000000 : ℝ)*X 0 2+(871176397/2000000000 : ℝ)*X 1 0+(4483102961/10000000000 : ℝ)*X 1 1+(423222259/1000000000 : ℝ)*X 1 2+(871176397/2000000000 : ℝ)*X 2 0+(4483102961/10000000000 : ℝ)*X 2 1+(423222259/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (192775799915947298309955891/33275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (566192377/50000000000000 : ℝ)*(base19) + (527224781/50000000000000 : ℝ)*(base23) + (41652427/100000000000000 : ℝ)*(lower2) + (29210207/20000000000000 : ℝ)*(upper3) + (22172317/25000000000000 : ℝ)*(upper5) + (597675819245479/10000000000000 : ℝ)*(major0) + (597675819245479/10000000000000 : ℝ)*(major1) + (597675819245479/10000000000000 : ℝ)*(major2) + (7987603021627923/100000000000000 : ℝ)*(sp0) + (798763311499339/10000000000000 : ℝ)*(sp1) + (7987633192928583/100000000000000 : ℝ)*(sp2) + (1982932598296891/50000000000000 : ℝ)*(sp3) + (15612875111/50000000000000 : ℝ)*(sp4) + (16747823889/100000000000000 : ℝ)*(sp7) + (396588194441767/10000000000000 : ℝ)*(f.failure) + (1597526849475629/20000000000000 : ℝ)*(f.sum) + (209901193763/1331000000000000000000000000 : ℝ)*base66 + (1563059692518514703/133100000000000000000000000000000 : ℝ)*base67 + (1084051589033614703/133100000000000000000000000000000 : ℝ)*base69 + (2077192317000914703/133100000000000000000000000000000 : ℝ)*base71 + (5027517705053/1331000000000000000000000000 : ℝ)*base74 + (115112228741385297/133100000000000000000000000000000 : ℝ)*base76 + (1978071006718414703/133100000000000000000000000000000 : ℝ)*base77 + (1663147227476914703/133100000000000000000000000000000 : ℝ)*base79 + (5148143325487/1331000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1374287/100000000000000000000 : ℝ)*base90 + (1374287/100000000000000000000 : ℝ)*base92 + (1374287/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94212283961504178246260049/15125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56380053/5000000000000 : ℝ)*(base19) + (1225398393/100000000000000 : ℝ)*(base23) + (125618363/100000000000000 : ℝ)*(upper3) + (44446259/100000000000000 : ℝ)*(lower4) + (31818971/25000000000000 : ℝ)*(upper5) + (3003510660033191/50000000000000 : ℝ)*(major0) + (3003510660033191/50000000000000 : ℝ)*(major1) + (3003510660033191/50000000000000 : ℝ)*(major2) + (31553040701/100000000000000 : ℝ)*(sp1) + (8477494069/25000000000000 : ℝ)*(sp2) + (8028079369272177/100000000000000 : ℝ)*(sp4) + (8028046688630417/100000000000000 : ℝ)*(sp5) + (8028044233897509/100000000000000 : ℝ)*(sp6) + (996490765807549/25000000000000 : ℝ)*(sp7) + (996490765807549/25000000000000 : ℝ)*(f.failure) + (8028079369272177/100000000000000 : ℝ)*(f.sum) + (204174833409/60500000000000000000000000 : ℝ)*base65 + (438061224571038317/60500000000000000000000000000000 : ℝ)*base67 + (1012734219384538317/60500000000000000000000000000000 : ℝ)*base69 + (284276751553038317/60500000000000000000000000000000 : ℝ)*base71 + (328910765331/121000000000000000000000000 : ℝ)*base73 + (757173857074538317/60500000000000000000000000000000 : ℝ)*base75 + (141641050663461683/60500000000000000000000000000000 : ℝ)*base78 + (1099290723836538317/60500000000000000000000000000000 : ℝ)*base79 + (70053181257/30250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2055989/250000000000000000000 : ℝ)*base90 + (2055989/250000000000000000000 : ℝ)*base92 + (2055989/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1205_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2857/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1205_s8_0 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-106855997/500000000 : ℝ)*x 0 + (5391842233/10000000000 : ℝ)*x 1 + (658342617/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106855997/500000000 : ℝ)^4199 ≤ (12992284535257/100000000000000 : ℝ)^3175 := by
    have hnat : (106855997 : ℕ)^4199*100000000000000^3175 ≤ 12992284535257^3175*500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106855997 500000000 12992284535257 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391842233/10000000000 : ℝ)^4199 ≤ (22089563748937/50000000000000 : ℝ)^3175 := by
    have hnat : (5391842233 : ℕ)^4199*50000000000000^3175 ≤ 22089563748937^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391842233 10000000000 22089563748937 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658342617/1250000000 : ℝ)^4199 ≤ (10707146987531/25000000000000 : ℝ)^3175 := by
    have hnat : (658342617 : ℕ)^4199*25000000000000^3175 ≤ 10707146987531^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658342617 1250000000 10707146987531 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-106855997/500000000 : ℝ), (5391842233/10000000000 : ℝ), (658342617/1250000000 : ℝ)] ![(12992284535257/100000000000000 : ℝ), (22089563748937/50000000000000 : ℝ), (10707146987531/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-106855997/500000000 : ℝ)|^4199 ≤ (12992284535257/100000000000000 : ℝ)^3175
        have hw : |(-106855997/500000000 : ℝ)|=(106855997/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391842233/10000000000 : ℝ)|^4199 ≤ (22089563748937/50000000000000 : ℝ)^3175
        have hw : |(5391842233/10000000000 : ℝ)|=(5391842233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658342617/1250000000 : ℝ)|^4199 ≤ (10707146987531/25000000000000 : ℝ)^3175
        have hw : |(658342617/1250000000 : ℝ)|=(658342617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s8_1 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267224171/500000000 : ℝ)*x 0 + (-2200557609/10000000000 : ℝ)*x 1 + (2633370463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267224171/500000000 : ℝ)^4199 ≤ (2183333012799/5000000000000 : ℝ)^3175 := by
    have hnat : (267224171 : ℕ)^4199*5000000000000^3175 ≤ 2183333012799^3175*500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267224171 500000000 2183333012799 5000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2200557609/10000000000 : ℝ)^4199 ≤ (2700950378331/20000000000000 : ℝ)^3175 := by
    have hnat : (2200557609 : ℕ)^4199*20000000000000^3175 ≤ 2700950378331^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200557609 10000000000 2700950378331 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633370463/5000000000 : ℝ)^4199 ≤ (21414293921289/50000000000000 : ℝ)^3175 := by
    have hnat : (2633370463 : ℕ)^4199*50000000000000^3175 ≤ 21414293921289^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633370463 5000000000 21414293921289 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267224171/500000000 : ℝ), (-2200557609/10000000000 : ℝ), (2633370463/5000000000 : ℝ)] ![(2183333012799/5000000000000 : ℝ), (2700950378331/20000000000000 : ℝ), (21414293921289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267224171/500000000 : ℝ)|^4199 ≤ (2183333012799/5000000000000 : ℝ)^3175
        have hw : |(267224171/500000000 : ℝ)|=(267224171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2200557609/10000000000 : ℝ)|^4199 ≤ (2700950378331/20000000000000 : ℝ)^3175
        have hw : |(-2200557609/10000000000 : ℝ)|=(2200557609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633370463/5000000000 : ℝ)|^4199 ≤ (21414293921289/50000000000000 : ℝ)^3175
        have hw : |(2633370463/5000000000 : ℝ)|=(2633370463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s8_2 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668060427/1250000000 : ℝ)*x 0 + (5266740931/10000000000 : ℝ)*x 1 + (-2200557607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668060427/1250000000 : ℝ)^4199 ≤ (21833330106379/50000000000000 : ℝ)^3175 := by
    have hnat : (668060427 : ℕ)^4199*50000000000000^3175 ≤ 21833330106379^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668060427 1250000000 21833330106379 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266740931/10000000000 : ℝ)^4199 ≤ (42828587896351/100000000000000 : ℝ)^3175 := by
    have hnat : (5266740931 : ℕ)^4199*100000000000000^3175 ≤ 42828587896351^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266740931 10000000000 42828587896351 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200557607/10000000000 : ℝ)^4199 ≤ (6752375937711/50000000000000 : ℝ)^3175 := by
    have hnat : (2200557607 : ℕ)^4199*50000000000000^3175 ≤ 6752375937711^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200557607 10000000000 6752375937711 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668060427/1250000000 : ℝ), (5266740931/10000000000 : ℝ), (-2200557607/10000000000 : ℝ)] ![(21833330106379/50000000000000 : ℝ), (42828587896351/100000000000000 : ℝ), (6752375937711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668060427/1250000000 : ℝ)|^4199 ≤ (21833330106379/50000000000000 : ℝ)^3175
        have hw : |(668060427/1250000000 : ℝ)|=(668060427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266740931/10000000000 : ℝ)|^4199 ≤ (42828587896351/100000000000000 : ℝ)^3175
        have hw : |(5266740931/10000000000 : ℝ)|=(5266740931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2200557607/10000000000 : ℝ)|^4199 ≤ (6752375937711/50000000000000 : ℝ)^3175
        have hw : |(-2200557607/10000000000 : ℝ)|=(2200557607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s8_3 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355874793/10000000000 : ℝ)*x 0 + (211583941/500000000 : ℝ)*x 1 + (4483643829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355874793/10000000000 : ℝ)^4199 ≤ (6663464542783/20000000000000 : ℝ)^3175 := by
    have hnat : (4355874793 : ℕ)^4199*20000000000000^3175 ≤ 6663464542783^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355874793 10000000000 6663464542783 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211583941/500000000 : ℝ)^4199 ≤ (6413360998123/20000000000000 : ℝ)^3175 := by
    have hnat : (211583941 : ℕ)^4199*20000000000000^3175 ≤ 6413360998123^3175*500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211583941 500000000 6413360998123 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483643829/10000000000 : ℝ)^4199 ≤ (34615872284831/100000000000000 : ℝ)^3175 := by
    have hnat : (4483643829 : ℕ)^4199*100000000000000^3175 ≤ 34615872284831^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483643829 10000000000 34615872284831 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355874793/10000000000 : ℝ), (211583941/500000000 : ℝ), (4483643829/10000000000 : ℝ)] ![(6663464542783/20000000000000 : ℝ), (6413360998123/20000000000000 : ℝ), (34615872284831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355874793/10000000000 : ℝ)|^4199 ≤ (6663464542783/20000000000000 : ℝ)^3175
        have hw : |(4355874793/10000000000 : ℝ)|=(4355874793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211583941/500000000 : ℝ)|^4199 ≤ (6413360998123/20000000000000 : ℝ)^3175
        have hw : |(211583941/500000000 : ℝ)|=(211583941/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483643829/10000000000 : ℝ)|^4199 ≤ (34615872284831/100000000000000 : ℝ)^3175
        have hw : |(4483643829/10000000000 : ℝ)|=(4483643829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s8_4 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2137124671/10000000000 : ℝ)*x 0 + (1316763941/2500000000 : ℝ)*x 1 + (673940783/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137124671/10000000000 : ℝ)^4199 ≤ (12992322572749/100000000000000 : ℝ)^3175 := by
    have hnat : (2137124671 : ℕ)^4199*100000000000000^3175 ≤ 12992322572749^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137124671 10000000000 12992322572749 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316763941/2500000000 : ℝ)^4199 ≤ (21415986914747/50000000000000 : ℝ)^3175 := by
    have hnat : (1316763941 : ℕ)^4199*50000000000000^3175 ≤ 21415986914747^3175*2500000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316763941 2500000000 21415986914747 50000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673940783/1250000000 : ℝ)^4199 ≤ (11043925896703/25000000000000 : ℝ)^3175 := by
    have hnat : (673940783 : ℕ)^4199*25000000000000^3175 ≤ 11043925896703^3175*1250000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673940783 1250000000 11043925896703 25000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2137124671/10000000000 : ℝ), (1316763941/2500000000 : ℝ), (673940783/1250000000 : ℝ)] ![(12992322572749/100000000000000 : ℝ), (21415986914747/50000000000000 : ℝ), (11043925896703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2137124671/10000000000 : ℝ)|^4199 ≤ (12992322572749/100000000000000 : ℝ)^3175
        have hw : |(-2137124671/10000000000 : ℝ)|=(2137124671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316763941/2500000000 : ℝ)|^4199 ≤ (21415986914747/50000000000000 : ℝ)^3175
        have hw : |(1316763941/2500000000 : ℝ)|=(1316763941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673940783/1250000000 : ℝ)|^4199 ≤ (11043925896703/25000000000000 : ℝ)^3175
        have hw : |(673940783/1250000000 : ℝ)|=(673940783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s8_5 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312644259/10000000000 : ℝ)*x 0 + (-1037886139/5000000000 : ℝ)*x 1 + (2695763131/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312644259/10000000000 : ℝ)^4199 ≤ (43322951957329/100000000000000 : ℝ)^3175 := by
    have hnat : (5312644259 : ℕ)^4199*100000000000000^3175 ≤ 43322951957329^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312644259 10000000000 43322951957329 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037886139/5000000000 : ℝ)^4199 ≤ (390667014543/3125000000000 : ℝ)^3175 := by
    have hnat : (1037886139 : ℕ)^4199*3125000000000^3175 ≤ 390667014543^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037886139 5000000000 390667014543 3125000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695763131/5000000000 : ℝ)^4199 ≤ (2208785178257/5000000000000 : ℝ)^3175 := by
    have hnat : (2695763131 : ℕ)^4199*5000000000000^3175 ≤ 2208785178257^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695763131 5000000000 2208785178257 5000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312644259/10000000000 : ℝ), (-1037886139/5000000000 : ℝ), (2695763131/5000000000 : ℝ)] ![(43322951957329/100000000000000 : ℝ), (390667014543/3125000000000 : ℝ), (2208785178257/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312644259/10000000000 : ℝ)|^4199 ≤ (43322951957329/100000000000000 : ℝ)^3175
        have hw : |(5312644259/10000000000 : ℝ)|=(5312644259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1037886139/5000000000 : ℝ)|^4199 ≤ (390667014543/3125000000000 : ℝ)^3175
        have hw : |(-1037886139/5000000000 : ℝ)|=(1037886139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695763131/5000000000 : ℝ)|^4199 ≤ (2208785178257/5000000000000 : ℝ)^3175
        have hw : |(2695763131/5000000000 : ℝ)|=(2695763131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s8_6 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656322129/5000000000 : ℝ)*x 0 + (5391526263/10000000000 : ℝ)*x 1 + (-1037886139/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656322129/5000000000 : ℝ)^4199 ≤ (8664590389309/20000000000000 : ℝ)^3175 := by
    have hnat : (2656322129 : ℕ)^4199*20000000000000^3175 ≤ 8664590389309^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656322129 5000000000 8664590389309 20000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391526263/10000000000 : ℝ)^4199 ≤ (5521962946997/12500000000000 : ℝ)^3175 := by
    have hnat : (5391526263 : ℕ)^4199*12500000000000^3175 ≤ 5521962946997^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391526263 10000000000 5521962946997 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037886139/5000000000 : ℝ)^4199 ≤ (390667014543/3125000000000 : ℝ)^3175 := by
    have hnat : (1037886139 : ℕ)^4199*3125000000000^3175 ≤ 390667014543^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037886139 5000000000 390667014543 3125000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656322129/5000000000 : ℝ), (5391526263/10000000000 : ℝ), (-1037886139/5000000000 : ℝ)] ![(8664590389309/20000000000000 : ℝ), (5521962946997/12500000000000 : ℝ), (390667014543/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656322129/5000000000 : ℝ)|^4199 ≤ (8664590389309/20000000000000 : ℝ)^3175
        have hw : |(2656322129/5000000000 : ℝ)|=(2656322129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391526263/10000000000 : ℝ)|^4199 ≤ (5521962946997/12500000000000 : ℝ)^3175
        have hw : |(5391526263/10000000000 : ℝ)|=(5391526263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037886139/5000000000 : ℝ)|^4199 ≤ (390667014543/3125000000000 : ℝ)^3175
        have hw : |(-1037886139/5000000000 : ℝ)|=(1037886139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1205_s8_7 (p : ℝ) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355884321/10000000000 : ℝ)*x 0 + (2241504863/5000000000 : ℝ)*x 1 + (846463043/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355884321/10000000000 : ℝ)^4199 ≤ (33317419096541/100000000000000 : ℝ)^3175 := by
    have hnat : (4355884321 : ℕ)^4199*100000000000000^3175 ≤ 33317419096541^3175*10000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355884321 10000000000 33317419096541 100000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241504863/5000000000 : ℝ)^4199 ≤ (3460939793411/10000000000000 : ℝ)^3175 := by
    have hnat : (2241504863 : ℕ)^4199*10000000000000^3175 ≤ 3460939793411^3175*5000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241504863 5000000000 3460939793411 10000000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846463043/2000000000 : ℝ)^4199 ≤ (4009147869997/12500000000000 : ℝ)^3175 := by
    have hnat : (846463043 : ℕ)^4199*12500000000000^3175 ≤ 4009147869997^3175*2000000000^4199 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846463043 2000000000 4009147869997 12500000000000 4199 3175 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4199/1024 : ℝ)) 4199 3175 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355884321/10000000000 : ℝ), (2241504863/5000000000 : ℝ), (846463043/2000000000 : ℝ)] ![(33317419096541/100000000000000 : ℝ), (3460939793411/10000000000000 : ℝ), (4009147869997/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355884321/10000000000 : ℝ)|^4199 ≤ (33317419096541/100000000000000 : ℝ)^3175
        have hw : |(4355884321/10000000000 : ℝ)|=(4355884321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241504863/5000000000 : ℝ)|^4199 ≤ (3460939793411/10000000000000 : ℝ)^3175
        have hw : |(2241504863/5000000000 : ℝ)|=(2241504863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846463043/2000000000 : ℝ)|^4199 ≤ (4009147869997/12500000000000 : ℝ)^3175
        have hw : |(846463043/2000000000 : ℝ)|=(846463043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1205_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5717/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3521/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11433/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11433/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11433/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11433/100000 : ℝ) ^ (8397/2048 : ℝ) ≤ (13751968147900107/100000000000000000000 : ℝ) := by
    have hpowers : (11433/100000 : ℝ)^8397 ≤ (13751968147900107/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11433 : ℕ)^8397*100000000000000000000^2048 ≤ 13751968147900107^2048*100000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11433 100000 13751968147900107 100000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11433/100000 : ℝ)) (X := (13751968147900107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2817/20000 : ℝ) ^ (8397/2048 : ℝ) ≤ (16172976873909033/50000000000000000000 : ℝ) := by
    have hpowers : (2817/20000 : ℝ)^8397 ≤ (16172976873909033/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2817 : ℕ)^8397*50000000000000000000^2048 ≤ 16172976873909033^2048*20000^8397 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 20000 16172976873909033 50000000000000000000 8397 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/20000 : ℝ)) (X := (16172976873909033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013751968147900107/50000000000000000000 : ℝ) ≤ (4883140010741/4882812500000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (50013751968147900107/50000000000000000000 : ℝ)^2048 ≤ (4883140010741/4882812500000 : ℝ)^8397 := by
      have hnat : (50013751968147900107 : ℕ)^2048*4882812500000^8397 ≤ 4883140010741^8397*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013751968147900107 50000000000000000000 4883140010741 4882812500000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (4883140010741/4882812500000 : ℝ)) (X := (50013751968147900107/50000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046097921895718173/100000000000000000000 : ℝ) ≤ (10001124116893283/10000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (100046097921895718173/100000000000000000000 : ℝ)^2048 ≤ (10001124116893283/10000000000000000 : ℝ)^8397 := by
      have hnat : (100046097921895718173 : ℕ)^2048*10000000000000000^8397 ≤ 10001124116893283^8397*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046097921895718173 100000000000000000000 10001124116893283 10000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001124116893283/10000000000000000 : ℝ)) (X := (100046097921895718173/100000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016172976873909033/25000000000000000000 : ℝ) ≤ (5000788745894499/5000000000000000 : ℝ) ^ (8397/2048 : ℝ) := by
    have hpowers : (25016172976873909033/25000000000000000000 : ℝ)^2048 ≤ (5000788745894499/5000000000000000 : ℝ)^8397 := by
      have hnat : (25016172976873909033 : ℕ)^2048*5000000000000000^8397 ≤ 5000788745894499^8397*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016172976873909033 25000000000000000000 5000788745894499 5000000000000000 2048 8397 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000788745894499/5000000000000000 : ℝ)) (X := (25016172976873909033/25000000000000000000 : ℝ)) (by norm_num) 8397 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13751968147900107/100000000000000000000 : ℝ) ≤ ((4418568656235355191/4420000000000000000 : ℝ)+2*(90674979143/53040000000000 : ℝ)*(11433/100000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (4418568656235355191/4420000000000000000 : ℝ)+2*(90674979143/53040000000000 : ℝ)*(11433/100000 : ℝ)=(4883140010741/4882812500000 : ℝ) by norm_num, show 1+2*(13751968147900107/100000000000000000000 : ℝ)=(50013751968147900107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16172976873909033/50000000000000000000 : ℝ)+(13751968147900107/100000000000000000000 : ℝ) ≤ ((4418568656235355191/4420000000000000000 : ℝ)+(90674979143/53040000000000 : ℝ)*((2817/20000 : ℝ)+(11433/100000 : ℝ)))^(8397/2048 : ℝ) := by
    rw [show (4418568656235355191/4420000000000000000 : ℝ)+(90674979143/53040000000000 : ℝ)*((2817/20000 : ℝ)+(11433/100000 : ℝ))=(10001124116893283/10000000000000000 : ℝ) by norm_num, show 1+(16172976873909033/50000000000000000000 : ℝ)+(13751968147900107/100000000000000000000 : ℝ)=(100046097921895718173/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16172976873909033/50000000000000000000 : ℝ) ≤ ((4418568656235355191/4420000000000000000 : ℝ)+2*(90674979143/53040000000000 : ℝ)*(2817/20000 : ℝ))^(8397/2048 : ℝ) := by
    rw [show (4418568656235355191/4420000000000000000 : ℝ)+2*(90674979143/53040000000000 : ℝ)*(2817/20000 : ℝ)=(5000788745894499/5000000000000000 : ℝ) by norm_num, show 1+2*(16172976873909033/50000000000000000000 : ℝ)=(25016172976873909033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4418568656235355191/4420000000000000000 : ℝ)*(X 1 0+X 2 0)+(90674979143/53040000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (4418568656235355191/4420000000000000000 : ℝ)) (alpha := (90674979143/53040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4418568656235355191/4420000000000000000 : ℝ)*(X 0 1+X 2 1)+(90674979143/53040000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (4418568656235355191/4420000000000000000 : ℝ)) (alpha := (90674979143/53040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4418568656235355191/4420000000000000000 : ℝ)*(X 0 2+X 1 2)+(90674979143/53040000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8397/2048 : ℝ)) (lo := (11433/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (4418568656235355191/4420000000000000000 : ℝ)) (alpha := (90674979143/53040000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-106855997/500000000 : ℝ)*X 0 0+(5391842233/10000000000 : ℝ)*X 0 1+(658342617/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267224171/500000000 : ℝ)*X 1 0+(-2200557609/10000000000 : ℝ)*X 1 1+(2633370463/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668060427/1250000000 : ℝ)*X 2 0+(5266740931/10000000000 : ℝ)*X 2 1+(-2200557607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355874793/10000000000 : ℝ)*X 0 0+(211583941/500000000 : ℝ)*X 0 1+(4483643829/10000000000 : ℝ)*X 0 2+(4355874793/10000000000 : ℝ)*X 1 0+(211583941/500000000 : ℝ)*X 1 1+(4483643829/10000000000 : ℝ)*X 1 2+(4355874793/10000000000 : ℝ)*X 2 0+(211583941/500000000 : ℝ)*X 2 1+(4483643829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2137124671/10000000000 : ℝ)*X 0 0+(1316763941/2500000000 : ℝ)*X 0 1+(673940783/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312644259/10000000000 : ℝ)*X 1 0+(-1037886139/5000000000 : ℝ)*X 1 1+(2695763131/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656322129/5000000000 : ℝ)*X 2 0+(5391526263/10000000000 : ℝ)*X 2 1+(-1037886139/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355884321/10000000000 : ℝ)*X 0 0+(2241504863/5000000000 : ℝ)*X 0 1+(846463043/2000000000 : ℝ)*X 0 2+(4355884321/10000000000 : ℝ)*X 1 0+(2241504863/5000000000 : ℝ)*X 1 1+(846463043/2000000000 : ℝ)*X 1 2+(4355884321/10000000000 : ℝ)*X 2 0+(2241504863/5000000000 : ℝ)*X 2 1+(846463043/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1205_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1214818485464062123860144831/221000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21625989/2000000000000 : ℝ)*(base19) + (250023491/25000000000000 : ℝ)*(base23) + (8040541/20000000000000 : ℝ)*(lower2) + (5449777/4000000000000 : ℝ)*(upper3) + (82569847/100000000000000 : ℝ)*(upper5) + (5981209004977551/100000000000000 : ℝ)*(major0) + (5981209004977551/100000000000000 : ℝ)*(major1) + (5981209004977551/100000000000000 : ℝ)*(major2) + (399677654326723/5000000000000 : ℝ)*(sp0) + (7993581461345089/100000000000000 : ℝ)*(sp1) + (319743261702023/4000000000000 : ℝ)*(sp2) + (1984409692217097/50000000000000 : ℝ)*(sp3) + (29456110079/100000000000000 : ℝ)*(sp4) + (15899645819/100000000000000 : ℝ)*(sp7) + (3968835284080013/100000000000000 : ℝ)*(f.failure) + (7993582542644539/100000000000000 : ℝ)*(f.sum) + (2494627676557/884000000000000000000000000 : ℝ)*base66 + (10127197150879067241/442000000000000000000000000000000 : ℝ)*base67 + (6424477793165067241/442000000000000000000000000000000 : ℝ)*base69 + (1696931632217067241/442000000000000000000000000000000 : ℝ)*base71 + (2075042238799/884000000000000000000000000 : ℝ)*base73 + (6342644588049067241/442000000000000000000000000000000 : ℝ)*base75 + (2859462431777067241/442000000000000000000000000000000 : ℝ)*base77 + (1359335622141067241/442000000000000000000000000000000 : ℝ)*base79 + (6089307089707/884000000000000000000000000 : ℝ)*base81 + (2964293/1000000000000000000000 : ℝ)*base90 + (2964293/1000000000000000000000 : ℝ)*base92 + (2964293/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (138436960493435244914092091/22100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (282403597/25000000000000 : ℝ)*(base19) + (61371853/5000000000000 : ℝ)*(base23) + (98643033/25000000000000 : ℝ)*(lower1) + (124400897/100000000000000 : ℝ)*(upper3) + (22706579/50000000000000 : ℝ)*(lower4) + (128250697/100000000000000 : ℝ)*(upper5) + (601145099228033/10000000000000 : ℝ)*(major0) + (601145099228033/10000000000000 : ℝ)*(major1) + (601145099228033/10000000000000 : ℝ)*(major2) + (2311603237/100000000000000 : ℝ)*(sp2) + (8033999400530469/100000000000000 : ℝ)*(sp4) + (8033998270916081/100000000000000 : ℝ)*(sp5) + (2008498965372543/25000000000000 : ℝ)*(sp6) + (997225593806579/25000000000000 : ℝ)*(sp7) + (997225593806579/25000000000000 : ℝ)*(f.failure) + (8033999400530469/100000000000000 : ℝ)*(f.sum) + (5322179538667/1326000000000000000000000000 : ℝ)*base66 + (5073175871644357909/132600000000000000000000000000000 : ℝ)*base67 + (1315374515338042091/132600000000000000000000000000000 : ℝ)*base70 + (2746934598878557909/132600000000000000000000000000000 : ℝ)*base71 + (3427400008153/1326000000000000000000000000 : ℝ)*base74 + (5001174810226357909/132600000000000000000000000000000 : ℝ)*base75 + (663831904262842091/132600000000000000000000000000000 : ℝ)*base78 + (327381088260157909/132600000000000000000000000000000 : ℝ)*base79 + (804031128959/265200000000000000000000000 : ℝ)*base82 + (1618181/250000000000000000000 : ℝ)*base89 + (1618181/250000000000000000000 : ℝ)*base91 + (1618181/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1205_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11433/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1205_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1205_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1205_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1205_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1205_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8397/2048 : ℝ) ≤ p) (hpb : p ≤ (4199/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15070439/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2823/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2851/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1205_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
