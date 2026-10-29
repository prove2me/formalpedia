-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1685_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:33:05.024992+00:00
-- url     : https://prove2.me/submissions/ded31c22-3229-402e-93ed-3810105e4db1

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
theorem support_rectangle_w1685_s0_0 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1413559457/10000000000 : ℝ)*x 0 + (5750783721/10000000000 : ℝ)*x 1 + (4931887599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1413559457/10000000000 : ℝ)^5103 ≤ (1081228057829/12500000000000 : ℝ)^4079 := by
    have hnat : (1413559457 : ℕ)^5103*12500000000000^4079 ≤ 1081228057829^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413559457 10000000000 1081228057829 12500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5750783721/10000000000 : ℝ)^5103 ≤ (50050503142361/100000000000000 : ℝ)^4079 := by
    have hnat : (5750783721 : ℕ)^5103*100000000000000^4079 ≤ 50050503142361^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5750783721 10000000000 50050503142361 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4931887599/10000000000 : ℝ)^5103 ≤ (41299672366323/100000000000000 : ℝ)^4079 := by
    have hnat : (4931887599 : ℕ)^5103*100000000000000^4079 ≤ 41299672366323^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4931887599 10000000000 41299672366323 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1413559457/10000000000 : ℝ), (5750783721/10000000000 : ℝ), (4931887599/10000000000 : ℝ)] ![(1081228057829/12500000000000 : ℝ), (50050503142361/100000000000000 : ℝ), (41299672366323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1413559457/10000000000 : ℝ)|^5103 ≤ (1081228057829/12500000000000 : ℝ)^4079
        have hw : |(-1413559457/10000000000 : ℝ)|=(1413559457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5750783721/10000000000 : ℝ)|^5103 ≤ (50050503142361/100000000000000 : ℝ)^4079
        have hw : |(5750783721/10000000000 : ℝ)|=(5750783721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4931887599/10000000000 : ℝ)|^5103 ≤ (41299672366323/100000000000000 : ℝ)^4079
        have hw : |(4931887599/10000000000 : ℝ)|=(4931887599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s0_1 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422291137/10000000000 : ℝ)*x 0 + (-186084317/1000000000 : ℝ)*x 1 + (1232972179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422291137/10000000000 : ℝ)^5103 ≤ (9299970591963/20000000000000 : ℝ)^4079 := by
    have hnat : (5422291137 : ℕ)^5103*20000000000000^4079 ≤ 9299970591963^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422291137 10000000000 9299970591963 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186084317/1000000000 : ℝ)^5103 ≤ (12200462951801/100000000000000 : ℝ)^4079 := by
    have hnat : (186084317 : ℕ)^5103*100000000000000^4079 ≤ 12200462951801^4079*1000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186084317 1000000000 12200462951801 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1232972179/2500000000 : ℝ)^5103 ≤ (1032492101707/2500000000000 : ℝ)^4079 := by
    have hnat : (1232972179 : ℕ)^5103*2500000000000^4079 ≤ 1032492101707^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232972179 2500000000 1032492101707 2500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422291137/10000000000 : ℝ), (-186084317/1000000000 : ℝ), (1232972179/2500000000 : ℝ)] ![(9299970591963/20000000000000 : ℝ), (12200462951801/100000000000000 : ℝ), (1032492101707/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422291137/10000000000 : ℝ)|^5103 ≤ (9299970591963/20000000000000 : ℝ)^4079
        have hw : |(5422291137/10000000000 : ℝ)|=(5422291137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186084317/1000000000 : ℝ)|^5103 ≤ (12200462951801/100000000000000 : ℝ)^4079
        have hw : |(-186084317/1000000000 : ℝ)|=(186084317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1232972179/2500000000 : ℝ)|^5103 ≤ (1032492101707/2500000000000 : ℝ)^4079
        have hw : |(1232972179/2500000000 : ℝ)|=(1232972179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s0_2 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1355573273/2500000000 : ℝ)*x 0 + (1232971903/2500000000 : ℝ)*x 1 + (-232605253/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1355573273/2500000000 : ℝ)^5103 ≤ (46499873934111/100000000000000 : ℝ)^4079 := by
    have hnat : (1355573273 : ℕ)^5103*100000000000000^4079 ≤ 46499873934111^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355573273 2500000000 46499873934111 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1232971903/2500000000 : ℝ)^5103 ≤ (20649836251257/50000000000000 : ℝ)^4079 := by
    have hnat : (1232971903 : ℕ)^5103*50000000000000^4079 ≤ 20649836251257^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232971903 2500000000 20649836251257 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (232605253/1250000000 : ℝ)^5103 ≤ (6100226775953/50000000000000 : ℝ)^4079 := by
    have hnat : (232605253 : ℕ)^5103*50000000000000^4079 ≤ 6100226775953^4079*1250000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      232605253 1250000000 6100226775953 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1355573273/2500000000 : ℝ), (1232971903/2500000000 : ℝ), (-232605253/1250000000 : ℝ)] ![(46499873934111/100000000000000 : ℝ), (20649836251257/50000000000000 : ℝ), (6100226775953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1355573273/2500000000 : ℝ)|^5103 ≤ (46499873934111/100000000000000 : ℝ)^4079
        have hw : |(1355573273/2500000000 : ℝ)|=(1355573273/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1232971903/2500000000 : ℝ)|^5103 ≤ (20649836251257/50000000000000 : ℝ)^4079
        have hw : |(1232971903/2500000000 : ℝ)|=(1232971903/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-232605253/1250000000 : ℝ)|^5103 ≤ (6100226775953/50000000000000 : ℝ)^4079
        have hw : |(-232605253/1250000000 : ℝ)|=(232605253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s0_3 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2030501709/5000000000 : ℝ)*x 0 + (1522422013/5000000000 : ℝ)*x 1 + (1321022059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030501709/5000000000 : ℝ)^5103 ≤ (32387984312027/100000000000000 : ℝ)^4079 := by
    have hnat : (2030501709 : ℕ)^5103*100000000000000^4079 ≤ 32387984312027^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030501709 5000000000 32387984312027 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1522422013/5000000000 : ℝ)^5103 ≤ (22590103890387/100000000000000 : ℝ)^4079 := by
    have hnat : (1522422013 : ℕ)^5103*100000000000000^4079 ≤ 22590103890387^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1522422013 5000000000 22590103890387 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1321022059/2500000000 : ℝ)^5103 ≤ (45021911786113/100000000000000 : ℝ)^4079 := by
    have hnat : (1321022059 : ℕ)^5103*100000000000000^4079 ≤ 45021911786113^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321022059 2500000000 45021911786113 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2030501709/5000000000 : ℝ), (1522422013/5000000000 : ℝ), (1321022059/2500000000 : ℝ)] ![(32387984312027/100000000000000 : ℝ), (22590103890387/100000000000000 : ℝ), (45021911786113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2030501709/5000000000 : ℝ)|^5103 ≤ (32387984312027/100000000000000 : ℝ)^4079
        have hw : |(2030501709/5000000000 : ℝ)|=(2030501709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1522422013/5000000000 : ℝ)|^5103 ≤ (22590103890387/100000000000000 : ℝ)^4079
        have hw : |(1522422013/5000000000 : ℝ)|=(1522422013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1321022059/2500000000 : ℝ)|^5103 ≤ (45021911786113/100000000000000 : ℝ)^4079
        have hw : |(1321022059/2500000000 : ℝ)|=(1321022059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s0_4 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-353916353/2500000000 : ℝ)*x 0 + (4952548017/10000000000 : ℝ)*x 1 + (2864701747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353916353/2500000000 : ℝ)^5103 ≤ (866594929991/10000000000000 : ℝ)^4079 := by
    have hnat : (353916353 : ℕ)^5103*10000000000000^4079 ≤ 866594929991^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353916353 2500000000 866594929991 10000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4952548017/10000000000 : ℝ)^5103 ≤ (10379057371719/25000000000000 : ℝ)^4079 := by
    have hnat : (4952548017 : ℕ)^5103*25000000000000^4079 ≤ 10379057371719^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4952548017 10000000000 10379057371719 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2864701747/5000000000 : ℝ)^5103 ≤ (24908910599117/50000000000000 : ℝ)^4079 := by
    have hnat : (2864701747 : ℕ)^5103*50000000000000^4079 ≤ 24908910599117^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2864701747 5000000000 24908910599117 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353916353/2500000000 : ℝ), (4952548017/10000000000 : ℝ), (2864701747/5000000000 : ℝ)] ![(866594929991/10000000000000 : ℝ), (10379057371719/25000000000000 : ℝ), (24908910599117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353916353/2500000000 : ℝ)|^5103 ≤ (866594929991/10000000000000 : ℝ)^4079
        have hw : |(-353916353/2500000000 : ℝ)|=(353916353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4952548017/10000000000 : ℝ)|^5103 ≤ (10379057371719/25000000000000 : ℝ)^4079
        have hw : |(4952548017/10000000000 : ℝ)|=(4952548017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2864701747/5000000000 : ℝ)|^5103 ≤ (24908910599117/50000000000000 : ℝ)^4079
        have hw : |(2864701747/5000000000 : ℝ)|=(2864701747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s0_5 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599854693/5000000000 : ℝ)*x 0 + (-106332777/1000000000 : ℝ)*x 1 + (1432350927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599854693/5000000000 : ℝ)^5103 ≤ (44124308423657/100000000000000 : ℝ)^4079 := by
    have hnat : (2599854693 : ℕ)^5103*100000000000000^4079 ≤ 44124308423657^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599854693 5000000000 44124308423657 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106332777/1000000000 : ℝ)^5103 ≤ (6057868032213/100000000000000 : ℝ)^4079 := by
    have hnat : (106332777 : ℕ)^5103*100000000000000^4079 ≤ 6057868032213^4079*1000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106332777 1000000000 6057868032213 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1432350927/2500000000 : ℝ)^5103 ≤ (12454455881529/25000000000000 : ℝ)^4079 := by
    have hnat : (1432350927 : ℕ)^5103*25000000000000^4079 ≤ 12454455881529^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1432350927 2500000000 12454455881529 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599854693/5000000000 : ℝ), (-106332777/1000000000 : ℝ), (1432350927/2500000000 : ℝ)] ![(44124308423657/100000000000000 : ℝ), (6057868032213/100000000000000 : ℝ), (12454455881529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599854693/5000000000 : ℝ)|^5103 ≤ (44124308423657/100000000000000 : ℝ)^4079
        have hw : |(2599854693/5000000000 : ℝ)|=(2599854693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106332777/1000000000 : ℝ)|^5103 ≤ (6057868032213/100000000000000 : ℝ)^4079
        have hw : |(-106332777/1000000000 : ℝ)|=(106332777/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1432350927/2500000000 : ℝ)|^5103 ≤ (12454455881529/25000000000000 : ℝ)^4079
        have hw : |(1432350927/2500000000 : ℝ)|=(1432350927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s0_6 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259985471/500000000 : ℝ)*x 0 + (1145880747/2000000000 : ℝ)*x 1 + (-1063327679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259985471/500000000 : ℝ)^5103 ≤ (44124308784609/100000000000000 : ℝ)^4079 := by
    have hnat : (259985471 : ℕ)^5103*100000000000000^4079 ≤ 44124308784609^4079*500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259985471 500000000 44124308784609 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1145880747/2000000000 : ℝ)^5103 ≤ (49817823819821/100000000000000 : ℝ)^4079 := by
    have hnat : (1145880747 : ℕ)^5103*100000000000000^4079 ≤ 49817823819821^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145880747 2000000000 49817823819821 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063327679/10000000000 : ℝ)^5103 ≤ (6057867383629/100000000000000 : ℝ)^4079 := by
    have hnat : (1063327679 : ℕ)^5103*100000000000000^4079 ≤ 6057867383629^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063327679 10000000000 6057867383629 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259985471/500000000 : ℝ), (1145880747/2000000000 : ℝ), (-1063327679/10000000000 : ℝ)] ![(44124308784609/100000000000000 : ℝ), (49817823819821/100000000000000 : ℝ), (6057867383629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259985471/500000000 : ℝ)|^5103 ≤ (44124308784609/100000000000000 : ℝ)^4079
        have hw : |(259985471/500000000 : ℝ)|=(259985471/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1145880747/2000000000 : ℝ)|^5103 ≤ (49817823819821/100000000000000 : ℝ)^4079
        have hw : |(1145880747/2000000000 : ℝ)|=(1145880747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063327679/10000000000 : ℝ)|^5103 ≤ (6057867383629/100000000000000 : ℝ)^4079
        have hw : |(-1063327679/10000000000 : ℝ)|=(1063327679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s0_7 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4066761739/10000000000 : ℝ)*x 0 + (261379609/500000000 : ℝ)*x 1 + (193956659/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4066761739/10000000000 : ℝ)^5103 ≤ (16222724136749/50000000000000 : ℝ)^4079 := by
    have hnat : (4066761739 : ℕ)^5103*50000000000000^4079 ≤ 16222724136749^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4066761739 10000000000 16222724136749 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261379609/500000000 : ℝ)^5103 ≤ (44420517815421/100000000000000 : ℝ)^4079 := by
    have hnat : (261379609 : ℕ)^5103*100000000000000^4079 ≤ 44420517815421^4079*500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261379609 500000000 44420517815421 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (193956659/625000000 : ℝ)^5103 ≤ (11567016945009/50000000000000 : ℝ)^4079 := by
    have hnat : (193956659 : ℕ)^5103*50000000000000^4079 ≤ 11567016945009^4079*625000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193956659 625000000 11567016945009 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4066761739/10000000000 : ℝ), (261379609/500000000 : ℝ), (193956659/625000000 : ℝ)] ![(16222724136749/50000000000000 : ℝ), (44420517815421/100000000000000 : ℝ), (11567016945009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4066761739/10000000000 : ℝ)|^5103 ≤ (16222724136749/50000000000000 : ℝ)^4079
        have hw : |(4066761739/10000000000 : ℝ)|=(4066761739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261379609/500000000 : ℝ)|^5103 ≤ (44420517815421/100000000000000 : ℝ)^4079
        have hw : |(261379609/500000000 : ℝ)|=(261379609/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(193956659/625000000 : ℝ)|^5103 ≤ (11567016945009/50000000000000 : ℝ)^4079
        have hw : |(193956659/625000000 : ℝ)|=(193956659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1685_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1053/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (22831/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (5095/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5095 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5095*1^1024 ≤ 0^1024*1^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5095/1024 : ℝ) ≤ (1047165411764569399/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5095 ≤ (1047165411764569399/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5095*100000000000000000000^1024 ≤ 1047165411764569399^1024*5^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1047165411764569399 100000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1047165411764569399/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5095 := by
      have hnat : (1 : ℕ)^1024*1^5095 ≤ 1^5095*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101047165411764569399/100000000000000000000 : ℝ) ≤ (626309910899951/625000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (101047165411764569399/100000000000000000000 : ℝ)^1024 ≤ (626309910899951/625000000000000 : ℝ)^5095 := by
      have hnat : (101047165411764569399 : ℕ)^1024*625000000000000^5095 ≤ 626309910899951^5095*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101047165411764569399 100000000000000000000 626309910899951 625000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626309910899951/625000000000000 : ℝ)) (X := (101047165411764569399/100000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51047165411764569399/50000000000000000000 : ℝ) ≤ (313809910899951/312500000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (51047165411764569399/50000000000000000000 : ℝ)^1024 ≤ (313809910899951/312500000000000 : ℝ)^5095 := by
      have hnat : (51047165411764569399 : ℕ)^1024*312500000000000^5095 ≤ 313809910899951^5095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51047165411764569399 50000000000000000000 313809910899951 312500000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313809910899951/312500000000000 : ℝ)) (X := (51047165411764569399/50000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1309910899951/250000000000000 : ℝ)*(0 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1309910899951/250000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1047165411764569399/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1309910899951/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5095/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1309910899951/250000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(626309910899951/625000000000000 : ℝ) by norm_num, show 1+(1047165411764569399/100000000000000000000 : ℝ)+(0 : ℝ)=(101047165411764569399/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1047165411764569399/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1309910899951/250000000000000 : ℝ)*(2/5 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1309910899951/250000000000000 : ℝ)*(2/5 : ℝ)=(313809910899951/312500000000000 : ℝ) by norm_num, show 1+2*(1047165411764569399/100000000000000000000 : ℝ)=(51047165411764569399/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1309910899951/250000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1309910899951/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1309910899951/250000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1309910899951/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1309910899951/250000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1309910899951/250000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1413559457/10000000000 : ℝ)*X 0 0+(5750783721/10000000000 : ℝ)*X 0 1+(4931887599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5422291137/10000000000 : ℝ)*X 1 0+(-186084317/1000000000 : ℝ)*X 1 1+(1232972179/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1355573273/2500000000 : ℝ)*X 2 0+(1232971903/2500000000 : ℝ)*X 2 1+(-232605253/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2030501709/5000000000 : ℝ)*X 0 0+(1522422013/5000000000 : ℝ)*X 0 1+(1321022059/2500000000 : ℝ)*X 0 2+(2030501709/5000000000 : ℝ)*X 1 0+(1522422013/5000000000 : ℝ)*X 1 1+(1321022059/2500000000 : ℝ)*X 1 2+(2030501709/5000000000 : ℝ)*X 2 0+(1522422013/5000000000 : ℝ)*X 2 1+(1321022059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-353916353/2500000000 : ℝ)*X 0 0+(4952548017/10000000000 : ℝ)*X 0 1+(2864701747/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2599854693/5000000000 : ℝ)*X 1 0+(-106332777/1000000000 : ℝ)*X 1 1+(1432350927/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((259985471/500000000 : ℝ)*X 2 0+(1145880747/2000000000 : ℝ)*X 2 1+(-1063327679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4066761739/10000000000 : ℝ)*X 0 0+(261379609/500000000 : ℝ)*X 0 1+(193956659/625000000 : ℝ)*X 0 2+(4066761739/10000000000 : ℝ)*X 1 0+(261379609/500000000 : ℝ)*X 1 1+(193956659/625000000 : ℝ)*X 1 2+(4066761739/10000000000 : ℝ)*X 2 0+(261379609/500000000 : ℝ)*X 2 1+(193956659/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2119170099296395465599/390625000000000000000000000 : ℝ) := by norm_num
    linear_combination (9018257/25000000000000 : ℝ)*(base1) + (212859761/25000000000000 : ℝ)*(base19) + (1199862739/100000000000000 : ℝ)*(base23) + (22966493/25000000000000 : ℝ)*(base24) + (42157219/20000000000000 : ℝ)*(upper5) + (104234399792241/12500000000000 : ℝ)*(major0) + (104234399792241/12500000000000 : ℝ)*(major1) + (104234399792241/12500000000000 : ℝ)*(major2) + (1221160033232627/100000000000000 : ℝ)*(sp0) + (305291510948473/25000000000000 : ℝ)*(sp1) + (48846624140169/4000000000000 : ℝ)*(sp2) + (223290699633297/50000000000000 : ℝ)*(sp3) + (6898073337/100000000000000 : ℝ)*(sp4) + (942633723/50000000000000 : ℝ)*(sp7) + (111645830151767/25000000000000 : ℝ)*(f.failure) + (152645861904117/12500000000000 : ℝ)*(f.sum) + (3174150713507/3125000000000000000000000000 : ℝ)*base65 + (24758098919809/3125000000000000000000000000 : ℝ)*base68 + (1737988669273/390625000000000000000000000 : ℝ)*base70 + (19978644451059/3125000000000000000000000000 : ℝ)*base72 + (490078676059/1562500000000000000000000000 : ℝ)*base74 + (7419505044809/3125000000000000000000000000 : ℝ)*base76 + (6741077251059/3125000000000000000000000000 : ℝ)*base78 + (7350514244809/3125000000000000000000000000 : ℝ)*base80 + (7980106755191/1562500000000000000000000000 : ℝ)*base81 + (7954673/2500000000000000000000 : ℝ)*base89 + (7954673/2500000000000000000000 : ℝ)*base91 + (7954673/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (105650154838588032049041/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1707831409/100000000000000 : ℝ)*(base19) + (1732897659/100000000000000 : ℝ)*(base23) + (44350489/100000000000000 : ℝ)*(base32) + (73277009/25000000000000 : ℝ)*(upper3) + (59331523/25000000000000 : ℝ)*(upper5) + (878993501213697/100000000000000 : ℝ)*(major0) + (878993501213697/100000000000000 : ℝ)*(major1) + (878993501213697/100000000000000 : ℝ)*(major2) + (581537347/10000000000000 : ℝ)*(sp1) + (6204260607/100000000000000 : ℝ)*(sp2) + (643620107043173/50000000000000 : ℝ)*(sp4) + (1287232690881467/100000000000000 : ℝ)*(sp5) + (1287232276928081/100000000000000 : ℝ)*(sp6) + (470746462256807/100000000000000 : ℝ)*(sp7) + (7355414165739/1562500000000 : ℝ)*(f.failure) + (643620107043173/50000000000000 : ℝ)*(f.sum) + (24329997433653/12500000000000000000000000000 : ℝ)*base66 + (69896909278847/25000000000000000000000000000 : ℝ)*base67 + (59795410471153/25000000000000000000000000000 : ℝ)*base70 + (225731762796153/25000000000000000000000000000 : ℝ)*base72 + (75037653203847/12500000000000000000000000000 : ℝ)*base73 + (110969191271153/25000000000000000000000000000 : ℝ)*base76 + (136800893096153/25000000000000000000000000000 : ℝ)*base78 + (243643269146153/25000000000000000000000000000 : ℝ)*base80 + (24265007316347/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (605241/156250000000000000000 : ℝ)*base89 + (605241/156250000000000000000 : ℝ)*base91 + (605241/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1685_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1053/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (22831/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1685_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1685_s1_0 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1501548557/10000000000 : ℝ)*x 0 + (5511445791/10000000000 : ℝ)*x 1 + (319606077/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1501548557/10000000000 : ℝ)^5103 ≤ (9328595124393/100000000000000 : ℝ)^4079 := by
    have hnat : (1501548557 : ℕ)^5103*100000000000000^4079 ≤ 9328595124393^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501548557 10000000000 9328595124393 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511445791/10000000000 : ℝ)^5103 ≤ (47458318221959/100000000000000 : ℝ)^4079 := by
    have hnat : (5511445791 : ℕ)^5103*100000000000000^4079 ≤ 47458318221959^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511445791 10000000000 47458318221959 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319606077/625000000 : ℝ)^5103 ≤ (10803271661433/25000000000000 : ℝ)^4079 := by
    have hnat : (319606077 : ℕ)^5103*25000000000000^4079 ≤ 10803271661433^4079*625000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319606077 625000000 10803271661433 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1501548557/10000000000 : ℝ), (5511445791/10000000000 : ℝ), (319606077/625000000 : ℝ)] ![(9328595124393/100000000000000 : ℝ), (47458318221959/100000000000000 : ℝ), (10803271661433/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1501548557/10000000000 : ℝ)|^5103 ≤ (9328595124393/100000000000000 : ℝ)^4079
        have hw : |(-1501548557/10000000000 : ℝ)|=(1501548557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511445791/10000000000 : ℝ)|^5103 ≤ (47458318221959/100000000000000 : ℝ)^4079
        have hw : |(5511445791/10000000000 : ℝ)|=(5511445791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319606077/625000000 : ℝ)|^5103 ≤ (10803271661433/25000000000000 : ℝ)^4079
        have hw : |(319606077/625000000 : ℝ)|=(319606077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s1_1 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679263177/5000000000 : ℝ)*x 0 + (-1709265829/10000000000 : ℝ)*x 1 + (2556848531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679263177/5000000000 : ℝ)^5103 ≤ (22908381369269/50000000000000 : ℝ)^4079 := by
    have hnat : (2679263177 : ℕ)^5103*50000000000000^4079 ≤ 22908381369269^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679263177 5000000000 22908381369269 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1709265829/10000000000 : ℝ)^5103 ≤ (2194030477787/20000000000000 : ℝ)^4079 := by
    have hnat : (1709265829 : ℕ)^5103*20000000000000^4079 ≤ 2194030477787^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709265829 10000000000 2194030477787 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2556848531/5000000000 : ℝ)^5103 ≤ (43213084848513/100000000000000 : ℝ)^4079 := by
    have hnat : (2556848531 : ℕ)^5103*100000000000000^4079 ≤ 43213084848513^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2556848531 5000000000 43213084848513 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679263177/5000000000 : ℝ), (-1709265829/10000000000 : ℝ), (2556848531/5000000000 : ℝ)] ![(22908381369269/50000000000000 : ℝ), (2194030477787/20000000000000 : ℝ), (43213084848513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679263177/5000000000 : ℝ)|^5103 ≤ (22908381369269/50000000000000 : ℝ)^4079
        have hw : |(2679263177/5000000000 : ℝ)|=(2679263177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1709265829/10000000000 : ℝ)|^5103 ≤ (2194030477787/20000000000000 : ℝ)^4079
        have hw : |(-1709265829/10000000000 : ℝ)|=(1709265829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2556848531/5000000000 : ℝ)|^5103 ≤ (43213084848513/100000000000000 : ℝ)^4079
        have hw : |(2556848531/5000000000 : ℝ)|=(2556848531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s1_2 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358525719/10000000000 : ℝ)*x 0 + (5113697629/10000000000 : ℝ)*x 1 + (-1709265929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358525719/10000000000 : ℝ)^5103 ≤ (45816755946117/100000000000000 : ℝ)^4079 := by
    have hnat : (5358525719 : ℕ)^5103*100000000000000^4079 ≤ 45816755946117^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358525719 10000000000 45816755946117 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5113697629/10000000000 : ℝ)^5103 ≤ (2700818177673/6250000000000 : ℝ)^4079 := by
    have hnat : (5113697629 : ℕ)^5103*6250000000000^4079 ≤ 2700818177673^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113697629 10000000000 2700818177673 6250000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1709265929/10000000000 : ℝ)^5103 ≤ (548507659593/5000000000000 : ℝ)^4079 := by
    have hnat : (1709265929 : ℕ)^5103*5000000000000^4079 ≤ 548507659593^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1709265929 10000000000 548507659593 5000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358525719/10000000000 : ℝ), (5113697629/10000000000 : ℝ), (-1709265929/10000000000 : ℝ)] ![(45816755946117/100000000000000 : ℝ), (2700818177673/6250000000000 : ℝ), (548507659593/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358525719/10000000000 : ℝ)|^5103 ≤ (45816755946117/100000000000000 : ℝ)^4079
        have hw : |(5358525719/10000000000 : ℝ)|=(5358525719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5113697629/10000000000 : ℝ)|^5103 ≤ (2700818177673/6250000000000 : ℝ)^4079
        have hw : |(5113697629/10000000000 : ℝ)|=(5113697629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1709265929/10000000000 : ℝ)|^5103 ≤ (548507659593/5000000000000 : ℝ)^4079
        have hw : |(-1709265929/10000000000 : ℝ)|=(1709265929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s1_3 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2066693231/5000000000 : ℝ)*x 0 + (903438383/2500000000 : ℝ)*x 1 + (1175345839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2066693231/5000000000 : ℝ)^5103 ≤ (4138974489703/12500000000000 : ℝ)^4079 := by
    have hnat : (2066693231 : ℕ)^5103*12500000000000^4079 ≤ 4138974489703^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066693231 5000000000 4138974489703 12500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903438383/2500000000 : ℝ)^5103 ≤ (3498626663977/12500000000000 : ℝ)^4079 := by
    have hnat : (903438383 : ℕ)^5103*12500000000000^4079 ≤ 3498626663977^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903438383 2500000000 3498626663977 12500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1175345839/2500000000 : ℝ)^5103 ≤ (9724797689683/25000000000000 : ℝ)^4079 := by
    have hnat : (1175345839 : ℕ)^5103*25000000000000^4079 ≤ 9724797689683^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1175345839 2500000000 9724797689683 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2066693231/5000000000 : ℝ), (903438383/2500000000 : ℝ), (1175345839/2500000000 : ℝ)] ![(4138974489703/12500000000000 : ℝ), (3498626663977/12500000000000 : ℝ), (9724797689683/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2066693231/5000000000 : ℝ)|^5103 ≤ (4138974489703/12500000000000 : ℝ)^4079
        have hw : |(2066693231/5000000000 : ℝ)|=(2066693231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903438383/2500000000 : ℝ)|^5103 ≤ (3498626663977/12500000000000 : ℝ)^4079
        have hw : |(903438383/2500000000 : ℝ)|=(903438383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1175345839/2500000000 : ℝ)|^5103 ≤ (9724797689683/25000000000000 : ℝ)^4079
        have hw : |(1175345839/2500000000 : ℝ)|=(1175345839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s1_4 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-750893281/5000000000 : ℝ)*x 0 + (511855861/1000000000 : ℝ)*x 1 + (1376625531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (750893281/5000000000 : ℝ)^5103 ≤ (4665222501963/50000000000000 : ℝ)^4079 := by
    have hnat : (750893281 : ℕ)^5103*50000000000000^4079 ≤ 4665222501963^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      750893281 5000000000 4665222501963 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (511855861/1000000000 : ℝ)^5103 ≤ (8652897334367/20000000000000 : ℝ)^4079 := by
    have hnat : (511855861 : ℕ)^5103*20000000000000^4079 ≤ 8652897334367^4079*1000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511855861 1000000000 8652897334367 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376625531/2500000000 : ℝ)^5103 ≤ (740704192207/1562500000000 : ℝ)^4079 := by
    have hnat : (1376625531 : ℕ)^5103*1562500000000^4079 ≤ 740704192207^4079*2500000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376625531 2500000000 740704192207 1562500000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-750893281/5000000000 : ℝ), (511855861/1000000000 : ℝ), (1376625531/2500000000 : ℝ)] ![(4665222501963/50000000000000 : ℝ), (8652897334367/20000000000000 : ℝ), (740704192207/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-750893281/5000000000 : ℝ)|^5103 ≤ (4665222501963/50000000000000 : ℝ)^4079
        have hw : |(-750893281/5000000000 : ℝ)|=(750893281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(511855861/1000000000 : ℝ)|^5103 ≤ (8652897334367/20000000000000 : ℝ)^4079
        have hw : |(511855861/1000000000 : ℝ)|=(511855861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376625531/2500000000 : ℝ)|^5103 ≤ (740704192207/1562500000000 : ℝ)^4079
        have hw : |(1376625531/2500000000 : ℝ)|=(1376625531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s1_5 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5252165281/10000000000 : ℝ)*x 0 + (-1316461627/10000000000 : ℝ)*x 1 + (1101300549/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5252165281/10000000000 : ℝ)^5103 ≤ (11170474042169/25000000000000 : ℝ)^4079 := by
    have hnat : (5252165281 : ℕ)^5103*25000000000000^4079 ≤ 11170474042169^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252165281 10000000000 11170474042169 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316461627/10000000000 : ℝ)^5103 ≤ (1978257206011/25000000000000 : ℝ)^4079 := by
    have hnat : (1316461627 : ℕ)^5103*25000000000000^4079 ≤ 1978257206011^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316461627 10000000000 1978257206011 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101300549/2000000000 : ℝ)^5103 ≤ (47405074989497/100000000000000 : ℝ)^4079 := by
    have hnat : (1101300549 : ℕ)^5103*100000000000000^4079 ≤ 47405074989497^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101300549 2000000000 47405074989497 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5252165281/10000000000 : ℝ), (-1316461627/10000000000 : ℝ), (1101300549/2000000000 : ℝ)] ![(11170474042169/25000000000000 : ℝ), (1978257206011/25000000000000 : ℝ), (47405074989497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5252165281/10000000000 : ℝ)|^5103 ≤ (11170474042169/25000000000000 : ℝ)^4079
        have hw : |(5252165281/10000000000 : ℝ)|=(5252165281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1316461627/10000000000 : ℝ)|^5103 ≤ (1978257206011/25000000000000 : ℝ)^4079
        have hw : |(-1316461627/10000000000 : ℝ)|=(1316461627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101300549/2000000000 : ℝ)|^5103 ≤ (47405074989497/100000000000000 : ℝ)^4079
        have hw : |(1101300549/2000000000 : ℝ)|=(1101300549/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s1_6 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2626082817/5000000000 : ℝ)*x 0 + (5506502683/10000000000 : ℝ)*x 1 + (-41139413/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2626082817/5000000000 : ℝ)^5103 ≤ (1396309372677/3125000000000 : ℝ)^4079 := by
    have hnat : (2626082817 : ℕ)^5103*3125000000000^4079 ≤ 1396309372677^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626082817 5000000000 1396309372677 3125000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5506502683/10000000000 : ℝ)^5103 ≤ (47405074321749/100000000000000 : ℝ)^4079 := by
    have hnat : (5506502683 : ℕ)^5103*100000000000000^4079 ≤ 47405074321749^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506502683 10000000000 47405074321749 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41139413/312500000 : ℝ)^5103 ≤ (1582605146681/20000000000000 : ℝ)^4079 := by
    have hnat : (41139413 : ℕ)^5103*20000000000000^4079 ≤ 1582605146681^4079*312500000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41139413 312500000 1582605146681 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2626082817/5000000000 : ℝ), (5506502683/10000000000 : ℝ), (-41139413/312500000 : ℝ)] ![(1396309372677/3125000000000 : ℝ), (47405074321749/100000000000000 : ℝ), (1582605146681/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2626082817/5000000000 : ℝ)|^5103 ≤ (1396309372677/3125000000000 : ℝ)^4079
        have hw : |(2626082817/5000000000 : ℝ)|=(2626082817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5506502683/10000000000 : ℝ)|^5103 ≤ (47405074321749/100000000000000 : ℝ)^4079
        have hw : |(5506502683/10000000000 : ℝ)|=(5506502683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41139413/312500000 : ℝ)|^5103 ≤ (1582605146681/20000000000000 : ℝ)^4079
        have hw : |(-41139413/312500000 : ℝ)|=(41139413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s1_7 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2067018709/5000000000 : ℝ)*x 0 + (937617833/2000000000 : ℝ)*x 1 + (362727079/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067018709/5000000000 : ℝ)^5103 ≤ (8279579960079/25000000000000 : ℝ)^4079 := by
    have hnat : (2067018709 : ℕ)^5103*25000000000000^4079 ≤ 8279579960079^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067018709 5000000000 8279579960079 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (937617833/2000000000 : ℝ)^5103 ≤ (19380815026667/50000000000000 : ℝ)^4079 := by
    have hnat : (937617833 : ℕ)^5103*50000000000000^4079 ≤ 19380815026667^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937617833 2000000000 19380815026667 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (362727079/1000000000 : ℝ)^5103 ≤ (28120050086261/100000000000000 : ℝ)^4079 := by
    have hnat : (362727079 : ℕ)^5103*100000000000000^4079 ≤ 28120050086261^4079*1000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      362727079 1000000000 28120050086261 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067018709/5000000000 : ℝ), (937617833/2000000000 : ℝ), (362727079/1000000000 : ℝ)] ![(8279579960079/25000000000000 : ℝ), (19380815026667/50000000000000 : ℝ), (28120050086261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067018709/5000000000 : ℝ)|^5103 ≤ (8279579960079/25000000000000 : ℝ)^4079
        have hw : |(2067018709/5000000000 : ℝ)|=(2067018709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(937617833/2000000000 : ℝ)|^5103 ≤ (19380815026667/50000000000000 : ℝ)^4079
        have hw : |(937617833/2000000000 : ℝ)|=(937617833/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(362727079/1000000000 : ℝ)|^5103 ≤ (28120050086261/100000000000000 : ℝ)^4079
        have hw : |(362727079/1000000000 : ℝ)|=(362727079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1685_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22831/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1053/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (933/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1779/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (22831/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1053/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (22831/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1053/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (22831/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1053/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (22831/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1053/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (22831/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1053/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (22831/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1053/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1053/20000 : ℝ) ^ (5095/1024 : ℝ) ≤ (43471811466499/100000000000000000000 : ℝ) := by
    have hpowers : (1053/20000 : ℝ)^5095 ≤ (43471811466499/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1053 : ℕ)^5095*100000000000000000000^1024 ≤ 43471811466499^1024*20000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1053 20000 43471811466499 100000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1053/20000 : ℝ)) (X := (43471811466499/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (22831/100000 : ℝ) ^ (5095/1024 : ℝ) ≤ (64311062181886137/100000000000000000000 : ℝ) := by
    have hpowers : (22831/100000 : ℝ)^5095 ≤ (64311062181886137/100000000000000000000 : ℝ)^1024 := by
      have hnat : (22831 : ℕ)^5095*100000000000000000000^1024 ≤ 64311062181886137^1024*100000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22831 100000 64311062181886137 100000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22831/100000 : ℝ)) (X := (64311062181886137/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000043471811466499/50000000000000000000 : ℝ) ≤ (5000000873702051/5000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (50000043471811466499/50000000000000000000 : ℝ)^1024 ≤ (5000000873702051/5000000000000000 : ℝ)^5095 := by
      have hnat : (50000043471811466499 : ℕ)^1024*5000000000000000^5095 ≤ 5000000873702051^5095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000043471811466499 50000000000000000000 5000000873702051 5000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000873702051/5000000000000000 : ℝ)) (X := (50000043471811466499/50000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25016088633498338159/25000000000000000000 : ℝ) ≤ (10001293073730033/10000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (25016088633498338159/25000000000000000000 : ℝ)^1024 ≤ (10001293073730033/10000000000000000 : ℝ)^5095 := by
      have hnat : (25016088633498338159 : ℕ)^1024*10000000000000000^5095 ≤ 10001293073730033^5095*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016088633498338159 25000000000000000000 10001293073730033 10000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001293073730033/10000000000000000 : ℝ)) (X := (25016088633498338159/25000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50064311062181886137/50000000000000000000 : ℝ) ≤ (2500646100013991/2500000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (50064311062181886137/50000000000000000000 : ℝ)^1024 ≤ (2500646100013991/2500000000000000 : ℝ)^5095 := by
      have hnat : (50064311062181886137 : ℕ)^1024*2500000000000000^5095 ≤ 2500646100013991^5095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50064311062181886137 50000000000000000000 2500646100013991 2500000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500646100013991/2500000000000000 : ℝ)) (X := (50064311062181886137/50000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(43471811466499/100000000000000000000 : ℝ) ≤ ((87823216514344201151/87830000000000000000 : ℝ)+2*(1291326325931/1756600000000000 : ℝ)*(1053/20000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (87823216514344201151/87830000000000000000 : ℝ)+2*(1291326325931/1756600000000000 : ℝ)*(1053/20000 : ℝ)=(5000000873702051/5000000000000000 : ℝ) by norm_num, show 1+2*(43471811466499/100000000000000000000 : ℝ)=(50000043471811466499/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64311062181886137/100000000000000000000 : ℝ)+(43471811466499/100000000000000000000 : ℝ) ≤ ((87823216514344201151/87830000000000000000 : ℝ)+(1291326325931/1756600000000000 : ℝ)*((22831/100000 : ℝ)+(1053/20000 : ℝ)))^(5095/1024 : ℝ) := by
    rw [show (87823216514344201151/87830000000000000000 : ℝ)+(1291326325931/1756600000000000 : ℝ)*((22831/100000 : ℝ)+(1053/20000 : ℝ))=(10001293073730033/10000000000000000 : ℝ) by norm_num, show 1+(64311062181886137/100000000000000000000 : ℝ)+(43471811466499/100000000000000000000 : ℝ)=(25016088633498338159/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64311062181886137/100000000000000000000 : ℝ) ≤ ((87823216514344201151/87830000000000000000 : ℝ)+2*(1291326325931/1756600000000000 : ℝ)*(22831/100000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (87823216514344201151/87830000000000000000 : ℝ)+2*(1291326325931/1756600000000000 : ℝ)*(22831/100000 : ℝ)=(2500646100013991/2500000000000000 : ℝ) by norm_num, show 1+2*(64311062181886137/100000000000000000000 : ℝ)=(50064311062181886137/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (87823216514344201151/87830000000000000000 : ℝ)*(X 1 0+X 2 0)+(1291326325931/1756600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (1053/20000 : ℝ)) (hi := (22831/100000 : ℝ)) (c := (87823216514344201151/87830000000000000000 : ℝ)) (alpha := (1291326325931/1756600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (87823216514344201151/87830000000000000000 : ℝ)*(X 0 1+X 2 1)+(1291326325931/1756600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (1053/20000 : ℝ)) (hi := (22831/100000 : ℝ)) (c := (87823216514344201151/87830000000000000000 : ℝ)) (alpha := (1291326325931/1756600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (87823216514344201151/87830000000000000000 : ℝ)*(X 0 2+X 1 2)+(1291326325931/1756600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (1053/20000 : ℝ)) (hi := (22831/100000 : ℝ)) (c := (87823216514344201151/87830000000000000000 : ℝ)) (alpha := (1291326325931/1756600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1501548557/10000000000 : ℝ)*X 0 0+(5511445791/10000000000 : ℝ)*X 0 1+(319606077/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2679263177/5000000000 : ℝ)*X 1 0+(-1709265829/10000000000 : ℝ)*X 1 1+(2556848531/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358525719/10000000000 : ℝ)*X 2 0+(5113697629/10000000000 : ℝ)*X 2 1+(-1709265929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2066693231/5000000000 : ℝ)*X 0 0+(903438383/2500000000 : ℝ)*X 0 1+(1175345839/2500000000 : ℝ)*X 0 2+(2066693231/5000000000 : ℝ)*X 1 0+(903438383/2500000000 : ℝ)*X 1 1+(1175345839/2500000000 : ℝ)*X 1 2+(2066693231/5000000000 : ℝ)*X 2 0+(903438383/2500000000 : ℝ)*X 2 1+(1175345839/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-750893281/5000000000 : ℝ)*X 0 0+(511855861/1000000000 : ℝ)*X 0 1+(1376625531/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5252165281/10000000000 : ℝ)*X 1 0+(-1316461627/10000000000 : ℝ)*X 1 1+(1101300549/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2626082817/5000000000 : ℝ)*X 2 0+(5506502683/10000000000 : ℝ)*X 2 1+(-41139413/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2067018709/5000000000 : ℝ)*X 0 0+(937617833/2000000000 : ℝ)*X 0 1+(362727079/1000000000 : ℝ)*X 0 2+(2067018709/5000000000 : ℝ)*X 1 0+(937617833/2000000000 : ℝ)*X 1 1+(362727079/1000000000 : ℝ)*X 1 2+(2067018709/5000000000 : ℝ)*X 2 0+(937617833/2000000000 : ℝ)*X 2 1+(362727079/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21289888935691296436845348201/4391500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18818117/2500000000000 : ℝ)*(base19) + (379492689/100000000000000 : ℝ)*(base23) + (39185431/25000000000000 : ℝ)*(upper3) + (806961/2000000000000 : ℝ)*(upper4) + (914571/50000000000000 : ℝ)*(upper5) + (1716798579228483/100000000000000 : ℝ)*(major0) + (1716798579228483/100000000000000 : ℝ)*(major1) + (1716798579228483/100000000000000 : ℝ)*(major2) + (1257079115295471/50000000000000 : ℝ)*(sp0) + (2514161762985863/100000000000000 : ℝ)*(sp1) + (1257081068108927/50000000000000 : ℝ)*(sp2) + (229858035833963/25000000000000 : ℝ)*(sp3) + (4285119601/100000000000000 : ℝ)*(sp4) + (2337811349/100000000000000 : ℝ)*(sp7) + (919434481147201/100000000000000 : ℝ)*(f.failure) + (1257081257855271/50000000000000 : ℝ)*(f.sum) + (129512717298827/87830000000000000000000000000 : ℝ)*base66 + (25583261936251233933/8783000000000000000000000000000000 : ℝ)*base67 + (14926167274704233933/8783000000000000000000000000000000 : ℝ)*base69 + (7566488276910233933/8783000000000000000000000000000000 : ℝ)*base71 + (200107355418413/87830000000000000000000000000 : ℝ)*base73 + (34613724479249766067/8783000000000000000000000000000000 : ℝ)*base76 + (22568454824381766067/8783000000000000000000000000000000 : ℝ)*base78 + (10473617300429233933/8783000000000000000000000000000000 : ℝ)*base79 + (458925569336193/87830000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1719881/10000000000000000000000 : ℝ)*base90 + (1719881/10000000000000000000000 : ℝ)*base92 + (1719881/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (60686432750571811381271318277/4391500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (386086299/25000000000000 : ℝ)*(base19) + (906025737/50000000000000 : ℝ)*(base23) + (99758281/25000000000000 : ℝ)*(upper3) + (16014569/100000000000000 : ℝ)*(lower4) + (394485797/100000000000000 : ℝ)*(upper5) + (1760182174697591/100000000000000 : ℝ)*(major0) + (1760182174697591/100000000000000 : ℝ)*(major1) + (1760182174697591/100000000000000 : ℝ)*(major2) + (180986769/1562500000000 : ℝ)*(sp1) + (7371011173/50000000000000 : ℝ)*(sp2) + (2577695247197171/100000000000000 : ℝ)*(sp4) + (1288841059849379/50000000000000 : ℝ)*(sp5) + (322209836640419/12500000000000 : ℝ)*(sp6) + (471334320781217/50000000000000 : ℝ)*(sp7) + (471334320781217/50000000000000 : ℝ)*(f.failure) + (2577695247197171/100000000000000 : ℝ)*(f.sum) + (204522746934921/87830000000000000000000000000 : ℝ)*base65 + (2486993637150177241/8783000000000000000000000000000000 : ℝ)*base67 + (61123407030398177241/8783000000000000000000000000000000 : ℝ)*base69 + (25764482328168177241/8783000000000000000000000000000000 : ℝ)*base71 + (63593520020179/87830000000000000000000000000 : ℝ)*base74 + (134049965593264177241/8783000000000000000000000000000000 : ℝ)*base75 + (55994062345671822759/8783000000000000000000000000000000 : ℝ)*base78 + (5009110136269822759/8783000000000000000000000000000000 : ℝ)*base80 + (656302869217201/87830000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (38900777/5000000000000000000000 : ℝ)*base90 + (38900777/5000000000000000000000 : ℝ)*base92 + (38900777/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1685_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (22831/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1053/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (933/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1779/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1685_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1685_s2_0 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-753730373/5000000000 : ℝ)*x 0 + (1097580807/2000000000 : ℝ)*x 1 + (5133314847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (753730373/5000000000 : ℝ)^5103 ≤ (9374569031231/100000000000000 : ℝ)^4079 := by
    have hnat : (753730373 : ℕ)^5103*100000000000000^4079 ≤ 9374569031231^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753730373 5000000000 9374569031231 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097580807/2000000000 : ℝ)^5103 ≤ (9440969901643/20000000000000 : ℝ)^4079 := by
    have hnat : (1097580807 : ℕ)^5103*20000000000000^4079 ≤ 9440969901643^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097580807 2000000000 9440969901643 20000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133314847/10000000000 : ℝ)^5103 ≤ (5427572681179/12500000000000 : ℝ)^4079 := by
    have hnat : (5133314847 : ℕ)^5103*12500000000000^4079 ≤ 5427572681179^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133314847 10000000000 5427572681179 12500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-753730373/5000000000 : ℝ), (1097580807/2000000000 : ℝ), (5133314847/10000000000 : ℝ)] ![(9374569031231/100000000000000 : ℝ), (9440969901643/20000000000000 : ℝ), (5427572681179/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-753730373/5000000000 : ℝ)|^5103 ≤ (9374569031231/100000000000000 : ℝ)^4079
        have hw : |(-753730373/5000000000 : ℝ)|=(753730373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097580807/2000000000 : ℝ)|^5103 ≤ (9440969901643/20000000000000 : ℝ)^4079
        have hw : |(1097580807/2000000000 : ℝ)|=(1097580807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133314847/10000000000 : ℝ)|^5103 ≤ (5427572681179/12500000000000 : ℝ)^4079
        have hw : |(5133314847/10000000000 : ℝ)|=(5133314847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s2_1 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334514597/625000000 : ℝ)*x 0 + (-1691782799/10000000000 : ℝ)*x 1 + (5133314921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334514597/625000000 : ℝ)^5103 ≤ (22874730140851/50000000000000 : ℝ)^4079 := by
    have hnat : (334514597 : ℕ)^5103*50000000000000^4079 ≤ 22874730140851^4079*625000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334514597 625000000 22874730140851 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1691782799/10000000000 : ℝ)^5103 ≤ (2707489369831/25000000000000 : ℝ)^4079 := by
    have hnat : (1691782799 : ℕ)^5103*25000000000000^4079 ≤ 2707489369831^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691782799 10000000000 2707489369831 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5133314921/10000000000 : ℝ)^5103 ≤ (43420582232503/100000000000000 : ℝ)^4079 := by
    have hnat : (5133314921 : ℕ)^5103*100000000000000^4079 ≤ 43420582232503^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133314921 10000000000 43420582232503 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334514597/625000000 : ℝ), (-1691782799/10000000000 : ℝ), (5133314921/10000000000 : ℝ)] ![(22874730140851/50000000000000 : ℝ), (2707489369831/25000000000000 : ℝ), (43420582232503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334514597/625000000 : ℝ)|^5103 ≤ (22874730140851/50000000000000 : ℝ)^4079
        have hw : |(334514597/625000000 : ℝ)|=(334514597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1691782799/10000000000 : ℝ)|^5103 ≤ (2707489369831/25000000000000 : ℝ)^4079
        have hw : |(-1691782799/10000000000 : ℝ)|=(1691782799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5133314921/10000000000 : ℝ)|^5103 ≤ (43420582232503/100000000000000 : ℝ)^4079
        have hw : |(5133314921/10000000000 : ℝ)|=(5133314921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s2_2 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352233789/10000000000 : ℝ)*x 0 + (5133314583/10000000000 : ℝ)*x 1 + (-105736433/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352233789/10000000000 : ℝ)^5103 ≤ (45749462816079/100000000000000 : ℝ)^4079 := by
    have hnat : (5352233789 : ℕ)^5103*100000000000000^4079 ≤ 45749462816079^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352233789 10000000000 45749462816079 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5133314583/10000000000 : ℝ)^5103 ≤ (10855144663943/25000000000000 : ℝ)^4079 := by
    have hnat : (5133314583 : ℕ)^5103*25000000000000^4079 ≤ 10855144663943^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5133314583 10000000000 10855144663943 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105736433/625000000 : ℝ)^5103 ≤ (10829958512427/100000000000000 : ℝ)^4079 := by
    have hnat : (105736433 : ℕ)^5103*100000000000000^4079 ≤ 10829958512427^4079*625000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105736433 625000000 10829958512427 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352233789/10000000000 : ℝ), (5133314583/10000000000 : ℝ), (-105736433/625000000 : ℝ)] ![(45749462816079/100000000000000 : ℝ), (10855144663943/25000000000000 : ℝ), (10829958512427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352233789/10000000000 : ℝ)|^5103 ≤ (45749462816079/100000000000000 : ℝ)^4079
        have hw : |(5352233789/10000000000 : ℝ)|=(5352233789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5133314583/10000000000 : ℝ)|^5103 ≤ (10855144663943/25000000000000 : ℝ)^4079
        have hw : |(5133314583/10000000000 : ℝ)|=(5133314583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105736433/625000000 : ℝ)|^5103 ≤ (10829958512427/100000000000000 : ℝ)^4079
        have hw : |(-105736433/625000000 : ℝ)|=(105736433/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s2_3 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (827584861/2000000000 : ℝ)*x 0 + (1836167153/5000000000 : ℝ)*x 1 + (928389411/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (827584861/2000000000 : ℝ)^5103 ≤ (3315727983687/10000000000000 : ℝ)^4079 := by
    have hnat : (827584861 : ℕ)^5103*10000000000000^4079 ≤ 3315727983687^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      827584861 2000000000 3315727983687 10000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1836167153/5000000000 : ℝ)^5103 ≤ (22310766769/78125000000 : ℝ)^4079 := by
    have hnat : (1836167153 : ℕ)^5103*78125000000^4079 ≤ 22310766769^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836167153 5000000000 22310766769 78125000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928389411/2000000000 : ℝ)^5103 ≤ (4785617336063/12500000000000 : ℝ)^4079 := by
    have hnat : (928389411 : ℕ)^5103*12500000000000^4079 ≤ 4785617336063^4079*2000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928389411 2000000000 4785617336063 12500000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(827584861/2000000000 : ℝ), (1836167153/5000000000 : ℝ), (928389411/2000000000 : ℝ)] ![(3315727983687/10000000000000 : ℝ), (22310766769/78125000000 : ℝ), (4785617336063/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(827584861/2000000000 : ℝ)|^5103 ≤ (3315727983687/10000000000000 : ℝ)^4079
        have hw : |(827584861/2000000000 : ℝ)|=(827584861/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1836167153/5000000000 : ℝ)|^5103 ≤ (22310766769/78125000000 : ℝ)^4079
        have hw : |(1836167153/5000000000 : ℝ)|=(1836167153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(928389411/2000000000 : ℝ)|^5103 ≤ (4785617336063/12500000000000 : ℝ)^4079
        have hw : |(928389411/2000000000 : ℝ)|=(928389411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s2_4 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1507628911/10000000000 : ℝ)*x 0 + (2568591019/5000000000 : ℝ)*x 1 + (685497357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1507628911/10000000000 : ℝ)^5103 ≤ (2343969341479/25000000000000 : ℝ)^4079 := by
    have hnat : (1507628911 : ℕ)^5103*25000000000000^4079 ≤ 2343969341479^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1507628911 10000000000 2343969341479 25000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568591019/5000000000 : ℝ)^5103 ≤ (1738460324273/4000000000000 : ℝ)^4079 := by
    have hnat : (2568591019 : ℕ)^5103*4000000000000^4079 ≤ 1738460324273^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568591019 5000000000 1738460324273 4000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (685497357/1250000000 : ℝ)^5103 ≤ (47162614513911/100000000000000 : ℝ)^4079 := by
    have hnat : (685497357 : ℕ)^5103*100000000000000^4079 ≤ 47162614513911^4079*1250000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685497357 1250000000 47162614513911 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1507628911/10000000000 : ℝ), (2568591019/5000000000 : ℝ), (685497357/1250000000 : ℝ)] ![(2343969341479/25000000000000 : ℝ), (1738460324273/4000000000000 : ℝ), (47162614513911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1507628911/10000000000 : ℝ)|^5103 ≤ (2343969341479/25000000000000 : ℝ)^4079
        have hw : |(-1507628911/10000000000 : ℝ)|=(1507628911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568591019/5000000000 : ℝ)|^5103 ≤ (1738460324273/4000000000000 : ℝ)^4079
        have hw : |(2568591019/5000000000 : ℝ)|=(2568591019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(685497357/1250000000 : ℝ)|^5103 ≤ (47162614513911/100000000000000 : ℝ)^4079
        have hw : |(685497357/1250000000 : ℝ)|=(685497357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s2_5 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257483663/10000000000 : ℝ)*x 0 + (-670559683/5000000000 : ℝ)*x 1 + (2741989167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257483663/10000000000 : ℝ)^5103 ≤ (22369253516413/50000000000000 : ℝ)^4079 := by
    have hnat : (5257483663 : ℕ)^5103*50000000000000^4079 ≤ 22369253516413^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257483663 10000000000 22369253516413 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (670559683/5000000000 : ℝ)^5103 ≤ (8098884051627/100000000000000 : ℝ)^4079 := by
    have hnat : (670559683 : ℕ)^5103*100000000000000^4079 ≤ 8098884051627^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670559683 5000000000 8098884051627 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2741989167/5000000000 : ℝ)^5103 ≤ (23581304448843/50000000000000 : ℝ)^4079 := by
    have hnat : (2741989167 : ℕ)^5103*50000000000000^4079 ≤ 23581304448843^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2741989167 5000000000 23581304448843 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257483663/10000000000 : ℝ), (-670559683/5000000000 : ℝ), (2741989167/5000000000 : ℝ)] ![(22369253516413/50000000000000 : ℝ), (8098884051627/100000000000000 : ℝ), (23581304448843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257483663/10000000000 : ℝ)|^5103 ≤ (22369253516413/50000000000000 : ℝ)^4079
        have hw : |(5257483663/10000000000 : ℝ)|=(5257483663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-670559683/5000000000 : ℝ)|^5103 ≤ (8098884051627/100000000000000 : ℝ)^4079
        have hw : |(-670559683/5000000000 : ℝ)|=(670559683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2741989167/5000000000 : ℝ)|^5103 ≤ (23581304448843/50000000000000 : ℝ)^4079
        have hw : |(2741989167/5000000000 : ℝ)|=(2741989167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s2_6 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5257483707/10000000000 : ℝ)*x 0 + (219359127/400000000 : ℝ)*x 1 + (-134111953/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5257483707/10000000000 : ℝ)^5103 ≤ (22369253750619/50000000000000 : ℝ)^4079 := by
    have hnat : (5257483707 : ℕ)^5103*50000000000000^4079 ≤ 22369253750619^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257483707 10000000000 22369253750619 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219359127/400000000 : ℝ)^5103 ≤ (47162607186997/100000000000000 : ℝ)^4079 := by
    have hnat : (219359127 : ℕ)^5103*100000000000000^4079 ≤ 47162607186997^4079*400000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219359127 400000000 47162607186997 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134111953/1000000000 : ℝ)^5103 ≤ (4049442645317/50000000000000 : ℝ)^4079 := by
    have hnat : (134111953 : ℕ)^5103*50000000000000^4079 ≤ 4049442645317^4079*1000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134111953 1000000000 4049442645317 50000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5257483707/10000000000 : ℝ), (219359127/400000000 : ℝ), (-134111953/1000000000 : ℝ)] ![(22369253750619/50000000000000 : ℝ), (47162607186997/100000000000000 : ℝ), (4049442645317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5257483707/10000000000 : ℝ)|^5103 ≤ (22369253750619/50000000000000 : ℝ)^4079
        have hw : |(5257483707/10000000000 : ℝ)|=(5257483707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219359127/400000000 : ℝ)|^5103 ≤ (47162607186997/100000000000000 : ℝ)^4079
        have hw : |(219359127/400000000 : ℝ)|=(219359127/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-134111953/1000000000 : ℝ)|^5103 ≤ (4049442645317/50000000000000 : ℝ)^4079
        have hw : |(-134111953/1000000000 : ℝ)|=(134111953/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1685_s2_7 (p : ℝ) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2069192321/5000000000 : ℝ)*x 0 + (4631370989/10000000000 : ℝ)*x 1 + (368306963/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2069192321/5000000000 : ℝ)^5103 ≤ (33161894607959/100000000000000 : ℝ)^4079 := by
    have hnat : (2069192321 : ℕ)^5103*100000000000000^4079 ≤ 33161894607959^4079*5000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069192321 5000000000 33161894607959 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4631370989/10000000000 : ℝ)^5103 ≤ (152703380127/400000000000 : ℝ)^4079 := by
    have hnat : (4631370989 : ℕ)^5103*400000000000^4079 ≤ 152703380127^4079*10000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631370989 10000000000 152703380127 400000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368306963/1000000000 : ℝ)^5103 ≤ (28662260339413/100000000000000 : ℝ)^4079 := by
    have hnat : (368306963 : ℕ)^5103*100000000000000^4079 ≤ 28662260339413^4079*1000000000^5103 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368306963 1000000000 28662260339413 100000000000000 5103 4079 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5103/1024 : ℝ)) 5103 4079 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2069192321/5000000000 : ℝ), (4631370989/10000000000 : ℝ), (368306963/1000000000 : ℝ)] ![(33161894607959/100000000000000 : ℝ), (152703380127/400000000000 : ℝ), (28662260339413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2069192321/5000000000 : ℝ)|^5103 ≤ (33161894607959/100000000000000 : ℝ)^4079
        have hw : |(2069192321/5000000000 : ℝ)|=(2069192321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4631370989/10000000000 : ℝ)|^5103 ≤ (152703380127/400000000000 : ℝ)^4079
        have hw : |(4631370989/10000000000 : ℝ)|=(4631370989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(368306963/1000000000 : ℝ)|^5103 ≤ (28662260339413/100000000000000 : ℝ)^4079
        have hw : |(368306963/1000000000 : ℝ)|=(368306963/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1685_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1779/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (933/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (2439/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8649/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1779/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (933/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1779/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (933/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1779/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (933/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1779/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (933/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1779/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (933/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1779/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (933/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (933/10000 : ℝ) ^ (5095/1024 : ℝ) ≤ (749130695651771/100000000000000000000 : ℝ) := by
    have hpowers : (933/10000 : ℝ)^5095 ≤ (749130695651771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (933 : ℕ)^5095*100000000000000000000^1024 ≤ 749130695651771^1024*10000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        933 10000 749130695651771 100000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (933/10000 : ℝ)) (X := (749130695651771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1779/10000 : ℝ) ^ (5095/1024 : ℝ) ≤ (18586002519526713/100000000000000000000 : ℝ) := by
    have hpowers : (1779/10000 : ℝ)^5095 ≤ (18586002519526713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1779 : ℕ)^5095*100000000000000000000^1024 ≤ 18586002519526713^1024*10000^5095 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1779 10000 18586002519526713 100000000000000000000 5095 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1779/10000 : ℝ)) (X := (18586002519526713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000749130695651771/50000000000000000000 : ℝ) ≤ (10000030112080107/10000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (50000749130695651771/50000000000000000000 : ℝ)^1024 ≤ (10000030112080107/10000000000000000 : ℝ)^5095 := by
      have hnat : (50000749130695651771 : ℕ)^1024*10000000000000000^5095 ≤ 10000030112080107^5095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000749130695651771 50000000000000000000 10000030112080107 10000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030112080107/10000000000000000 : ℝ)) (X := (50000749130695651771/50000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004833783303794621/25000000000000000000 : ℝ) ≤ (10000388570111663/10000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (25004833783303794621/25000000000000000000 : ℝ)^1024 ≤ (10000388570111663/10000000000000000 : ℝ)^5095 := by
      have hnat : (25004833783303794621 : ℕ)^1024*10000000000000000^5095 ≤ 10000388570111663^5095*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004833783303794621 25000000000000000000 10000388570111663 10000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000388570111663/10000000000000000 : ℝ)) (X := (25004833783303794621/25000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018586002519526713/50000000000000000000 : ℝ) ≤ (10000747028143219/10000000000000000 : ℝ) ^ (5095/1024 : ℝ) := by
    have hpowers : (50018586002519526713/50000000000000000000 : ℝ)^1024 ≤ (10000747028143219/10000000000000000 : ℝ)^5095 := by
      have hnat : (50018586002519526713 : ℕ)^1024*10000000000000000^5095 ≤ 10000747028143219^5095*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018586002519526713 50000000000000000000 10000747028143219 10000000000000000 1024 5095 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000747028143219/10000000000000000 : ℝ)) (X := (50018586002519526713/50000000000000000000 : ℝ)) (by norm_num) 5095 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(749130695651771/100000000000000000000 : ℝ) ≤ ((1409892765355481171/1410000000000000000 : ℝ)+2*(89614507889/211500000000000 : ℝ)*(933/10000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (1409892765355481171/1410000000000000000 : ℝ)+2*(89614507889/211500000000000 : ℝ)*(933/10000 : ℝ)=(10000030112080107/10000000000000000 : ℝ) by norm_num, show 1+2*(749130695651771/100000000000000000000 : ℝ)=(50000749130695651771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18586002519526713/100000000000000000000 : ℝ)+(749130695651771/100000000000000000000 : ℝ) ≤ ((1409892765355481171/1410000000000000000 : ℝ)+(89614507889/211500000000000 : ℝ)*((1779/10000 : ℝ)+(933/10000 : ℝ)))^(5095/1024 : ℝ) := by
    rw [show (1409892765355481171/1410000000000000000 : ℝ)+(89614507889/211500000000000 : ℝ)*((1779/10000 : ℝ)+(933/10000 : ℝ))=(10000388570111663/10000000000000000 : ℝ) by norm_num, show 1+(18586002519526713/100000000000000000000 : ℝ)+(749130695651771/100000000000000000000 : ℝ)=(25004833783303794621/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18586002519526713/100000000000000000000 : ℝ) ≤ ((1409892765355481171/1410000000000000000 : ℝ)+2*(89614507889/211500000000000 : ℝ)*(1779/10000 : ℝ))^(5095/1024 : ℝ) := by
    rw [show (1409892765355481171/1410000000000000000 : ℝ)+2*(89614507889/211500000000000 : ℝ)*(1779/10000 : ℝ)=(10000747028143219/10000000000000000 : ℝ) by norm_num, show 1+2*(18586002519526713/100000000000000000000 : ℝ)=(50018586002519526713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1409892765355481171/1410000000000000000 : ℝ)*(X 1 0+X 2 0)+(89614507889/211500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (933/10000 : ℝ)) (hi := (1779/10000 : ℝ)) (c := (1409892765355481171/1410000000000000000 : ℝ)) (alpha := (89614507889/211500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1409892765355481171/1410000000000000000 : ℝ)*(X 0 1+X 2 1)+(89614507889/211500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (933/10000 : ℝ)) (hi := (1779/10000 : ℝ)) (c := (1409892765355481171/1410000000000000000 : ℝ)) (alpha := (89614507889/211500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1409892765355481171/1410000000000000000 : ℝ)*(X 0 2+X 1 2)+(89614507889/211500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5095/1024 : ℝ)) (lo := (933/10000 : ℝ)) (hi := (1779/10000 : ℝ)) (c := (1409892765355481171/1410000000000000000 : ℝ)) (alpha := (89614507889/211500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-753730373/5000000000 : ℝ)*X 0 0+(1097580807/2000000000 : ℝ)*X 0 1+(5133314847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334514597/625000000 : ℝ)*X 1 0+(-1691782799/10000000000 : ℝ)*X 1 1+(5133314921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352233789/10000000000 : ℝ)*X 2 0+(5133314583/10000000000 : ℝ)*X 2 1+(-105736433/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((827584861/2000000000 : ℝ)*X 0 0+(1836167153/5000000000 : ℝ)*X 0 1+(928389411/2000000000 : ℝ)*X 0 2+(827584861/2000000000 : ℝ)*X 1 0+(1836167153/5000000000 : ℝ)*X 1 1+(928389411/2000000000 : ℝ)*X 1 2+(827584861/2000000000 : ℝ)*X 2 0+(1836167153/5000000000 : ℝ)*X 2 1+(928389411/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1507628911/10000000000 : ℝ)*X 0 0+(2568591019/5000000000 : ℝ)*X 0 1+(685497357/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5257483663/10000000000 : ℝ)*X 1 0+(-670559683/5000000000 : ℝ)*X 1 1+(2741989167/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5257483707/10000000000 : ℝ)*X 2 0+(219359127/400000000 : ℝ)*X 2 1+(-134111953/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2069192321/5000000000 : ℝ)*X 0 0+(4631370989/10000000000 : ℝ)*X 0 1+(368306963/1000000000 : ℝ)*X 0 2+(2069192321/5000000000 : ℝ)*X 1 0+(4631370989/10000000000 : ℝ)*X 1 1+(368306963/1000000000 : ℝ)*X 1 2+(2069192321/5000000000 : ℝ)*X 2 0+(4631370989/10000000000 : ℝ)*X 2 1+(368306963/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1685_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34331130915399142069947143/3525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (358165253/25000000000000 : ℝ)*(base19) + (176115439/12500000000000 : ℝ)*(base23) + (79543389/100000000000000 : ℝ)*(lower2) + (132571843/50000000000000 : ℝ)*(upper3) + (11878869/12500000000000 : ℝ)*(upper5) + (192577143424511/10000000000000 : ℝ)*(major0) + (192577143424511/10000000000000 : ℝ)*(major1) + (192577143424511/10000000000000 : ℝ)*(major2) + (141008968383193/5000000000000 : ℝ)*(sp0) + (1410095426058939/50000000000000 : ℝ)*(sp1) + (2820190875855379/100000000000000 : ℝ)*(sp2) + (128918022636123/12500000000000 : ℝ)*(sp3) + (12917115031/100000000000000 : ℝ)*(sp4) + (243119123/4000000000000 : ℝ)*(sp7) + (1031350259067059/100000000000000 : ℝ)*(f.failure) + (2820192284778891/100000000000000 : ℝ)*(f.sum) + (6730280642377/2115000000000000000000000000 : ℝ)*base66 + (474339858554372857/42300000000000000000000000000000 : ℝ)*base68 + (299242340483072857/42300000000000000000000000000000 : ℝ)*base70 + (222066185063072857/42300000000000000000000000000000 : ℝ)*base72 + (10666700216497/2115000000000000000000000000 : ℝ)*base74 + (4423281768327143/42300000000000000000000000000000 : ℝ)*base75 + (89690804325572857/42300000000000000000000000000000 : ℝ)*base78 + (210768714176072857/42300000000000000000000000000000 : ℝ)*base80 + (335788233389/264375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (100048821/10000000000000000000000 : ℝ)*base89 + (100048821/10000000000000000000000 : ℝ)*base91 + (100048821/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (251634126796353444983968871/17625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (848694163/50000000000000 : ℝ)*(base19) + (988546301/50000000000000 : ℝ)*(base23) + (100504221/100000000000000 : ℝ)*(upper3) + (155223727/100000000000000 : ℝ)*(lower4) + (89166407/25000000000000 : ℝ)*(upper5) + (984512806990433/50000000000000 : ℝ)*(major0) + (984512806990433/50000000000000 : ℝ)*(major1) + (984512806990433/50000000000000 : ℝ)*(major2) + (14701261809/100000000000000 : ℝ)*(sp1) + (1562493147/12500000000000 : ℝ)*(sp2) + (360441955174743/12500000000000 : ℝ)*(sp4) + (2883519242747809/100000000000000 : ℝ)*(sp5) + (2883521164360167/100000000000000 : ℝ)*(sp6) + (210903022131999/20000000000000 : ℝ)*(sp7) + (210903022131999/20000000000000 : ℝ)*(f.failure) + (360441955174743/12500000000000 : ℝ)*(f.sum) + (895772046661/660937500000000000000000000 : ℝ)*base66 + (2782598766784151129/211500000000000000000000000000000 : ℝ)*base67 + (319996616033651129/211500000000000000000000000000000 : ℝ)*base69 + (1037609176507151129/211500000000000000000000000000000 : ℝ)*base71 + (4986218281031/2643750000000000000000000000 : ℝ)*base73 + (389527192177151129/211500000000000000000000000000000 : ℝ)*base75 + (867459330430151129/211500000000000000000000000000000 : ℝ)*base77 + (432566485467348871/211500000000000000000000000000000 : ℝ)*base80 + (19160855350013/5287500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (10615319/2000000000000000000000 : ℝ)*base90 + (10615319/2000000000000000000000 : ℝ)*base92 + (10615319/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1685_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1779/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (933/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2439/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1685_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1685_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2439/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1685_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1685_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1685_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5095/1024 : ℝ) ≤ p) (hpb : p ≤ (5103/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (186723319/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2439/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8649/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1685_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
