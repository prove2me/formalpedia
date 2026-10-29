-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1602_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:39:10.401907+00:00
-- url     : https://prove2.me/submissions/cf2e214c-98d5-4456-b510-055abc158695

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
theorem support_rectangle_w1602_s0_0 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-79037849/500000000 : ℝ)*x 0 + (5848050017/10000000000 : ℝ)*x 1 + (305435181/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (79037849/500000000 : ℝ)^4727 ≤ (9491289945727/100000000000000 : ℝ)^3703 := by
    have hnat : (79037849 : ℕ)^4727*100000000000000^3703 ≤ 9491289945727^3703*500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79037849 500000000 9491289945727 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5848050017/10000000000 : ℝ)^4727 ≤ (50417587399573/100000000000000 : ℝ)^3703 := by
    have hnat : (5848050017 : ℕ)^4727*100000000000000^3703 ≤ 50417587399573^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5848050017 10000000000 50417587399573 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305435181/625000000 : ℝ)^4727 ≤ (5011390330529/12500000000000 : ℝ)^3703 := by
    have hnat : (305435181 : ℕ)^4727*12500000000000^3703 ≤ 5011390330529^3703*625000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305435181 625000000 5011390330529 12500000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-79037849/500000000 : ℝ), (5848050017/10000000000 : ℝ), (305435181/625000000 : ℝ)] ![(9491289945727/100000000000000 : ℝ), (50417587399573/100000000000000 : ℝ), (5011390330529/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-79037849/500000000 : ℝ)|^4727 ≤ (9491289945727/100000000000000 : ℝ)^3703
        have hw : |(-79037849/500000000 : ℝ)|=(79037849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5848050017/10000000000 : ℝ)|^4727 ≤ (50417587399573/100000000000000 : ℝ)^3703
        have hw : |(5848050017/10000000000 : ℝ)|=(5848050017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(305435181/625000000 : ℝ)|^4727 ≤ (5011390330529/12500000000000 : ℝ)^3703
        have hw : |(305435181/625000000 : ℝ)|=(305435181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s0_1 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5457027163/10000000000 : ℝ)*x 0 + (-1056924031/5000000000 : ℝ)*x 1 + (1221740689/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5457027163/10000000000 : ℝ)^4727 ≤ (46154698860553/100000000000000 : ℝ)^3703 := by
    have hnat : (5457027163 : ℕ)^4727*100000000000000^3703 ≤ 46154698860553^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5457027163 10000000000 46154698860553 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056924031/5000000000 : ℝ)^4727 ≤ (6877089975867/50000000000000 : ℝ)^3703 := by
    have hnat : (1056924031 : ℕ)^4727*50000000000000^3703 ≤ 6877089975867^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056924031 5000000000 6877089975867 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1221740689/2500000000 : ℝ)^4727 ≤ (40091121178113/100000000000000 : ℝ)^3703 := by
    have hnat : (1221740689 : ℕ)^4727*100000000000000^3703 ≤ 40091121178113^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221740689 2500000000 40091121178113 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5457027163/10000000000 : ℝ), (-1056924031/5000000000 : ℝ), (1221740689/2500000000 : ℝ)] ![(46154698860553/100000000000000 : ℝ), (6877089975867/50000000000000 : ℝ), (40091121178113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5457027163/10000000000 : ℝ)|^4727 ≤ (46154698860553/100000000000000 : ℝ)^3703
        have hw : |(5457027163/10000000000 : ℝ)|=(5457027163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1056924031/5000000000 : ℝ)|^4727 ≤ (6877089975867/50000000000000 : ℝ)^3703
        have hw : |(-1056924031/5000000000 : ℝ)|=(1056924031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1221740689/2500000000 : ℝ)|^4727 ≤ (40091121178113/100000000000000 : ℝ)^3703
        have hw : |(1221740689/2500000000 : ℝ)|=(1221740689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s0_2 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (682128381/1250000000 : ℝ)*x 0 + (4886962803/10000000000 : ℝ)*x 1 + (-264231019/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (682128381/1250000000 : ℝ)^4727 ≤ (46154697618931/100000000000000 : ℝ)^3703 := by
    have hnat : (682128381 : ℕ)^4727*100000000000000^3703 ≤ 46154697618931^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682128381 1250000000 46154697618931 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4886962803/10000000000 : ℝ)^4727 ≤ (4009112167031/10000000000000 : ℝ)^3703 := by
    have hnat : (4886962803 : ℕ)^4727*10000000000000^3703 ≤ 4009112167031^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4886962803 10000000000 4009112167031 10000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264231019/1250000000 : ℝ)^4727 ≤ (3438545174819/25000000000000 : ℝ)^3703 := by
    have hnat : (264231019 : ℕ)^4727*25000000000000^3703 ≤ 3438545174819^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264231019 1250000000 3438545174819 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(682128381/1250000000 : ℝ), (4886962803/10000000000 : ℝ), (-264231019/1250000000 : ℝ)] ![(46154697618931/100000000000000 : ℝ), (4009112167031/10000000000000 : ℝ), (3438545174819/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(682128381/1250000000 : ℝ)|^4727 ≤ (46154697618931/100000000000000 : ℝ)^3703
        have hw : |(682128381/1250000000 : ℝ)|=(682128381/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4886962803/10000000000 : ℝ)|^4727 ≤ (4009112167031/10000000000000 : ℝ)^3703
        have hw : |(4886962803/10000000000 : ℝ)|=(4886962803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-264231019/1250000000 : ℝ)|^4727 ≤ (3438545174819/25000000000000 : ℝ)^3703
        have hw : |(-264231019/1250000000 : ℝ)|=(264231019/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s0_3 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1028431613/2500000000 : ℝ)*x 0 + (3073064291/10000000000 : ℝ)*x 1 + (1352481221/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028431613/2500000000 : ℝ)^4727 ≤ (32177992545373/100000000000000 : ℝ)^3703 := by
    have hnat : (1028431613 : ℕ)^4727*100000000000000^3703 ≤ 32177992545373^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028431613 2500000000 32177992545373 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3073064291/10000000000 : ℝ)^4727 ≤ (22175250336247/100000000000000 : ℝ)^3703 := by
    have hnat : (3073064291 : ℕ)^4727*100000000000000^3703 ≤ 22175250336247^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3073064291 10000000000 22175250336247 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352481221/2500000000 : ℝ)^4727 ≤ (1426461159477/3125000000000 : ℝ)^3703 := by
    have hnat : (1352481221 : ℕ)^4727*3125000000000^3703 ≤ 1426461159477^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352481221 2500000000 1426461159477 3125000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1028431613/2500000000 : ℝ), (3073064291/10000000000 : ℝ), (1352481221/2500000000 : ℝ)] ![(32177992545373/100000000000000 : ℝ), (22175250336247/100000000000000 : ℝ), (1426461159477/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1028431613/2500000000 : ℝ)|^4727 ≤ (32177992545373/100000000000000 : ℝ)^3703
        have hw : |(1028431613/2500000000 : ℝ)|=(1028431613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3073064291/10000000000 : ℝ)|^4727 ≤ (22175250336247/100000000000000 : ℝ)^3703
        have hw : |(3073064291/10000000000 : ℝ)|=(3073064291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352481221/2500000000 : ℝ)|^4727 ≤ (1426461159477/3125000000000 : ℝ)^3703
        have hw : |(1352481221/2500000000 : ℝ)|=(1352481221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s0_4 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1583661/10000000 : ℝ)*x 0 + (4911380383/10000000000 : ℝ)*x 1 + (2911380511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1583661/10000000 : ℝ)^4727 ≤ (4756776939151/50000000000000 : ℝ)^3703 := by
    have hnat : (1583661 : ℕ)^4727*50000000000000^3703 ≤ 4756776939151^3703*10000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583661 10000000 4756776939151 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4911380383/10000000000 : ℝ)^4727 ≤ (40347005739697/100000000000000 : ℝ)^3703 := by
    have hnat : (4911380383 : ℕ)^4727*100000000000000^3703 ≤ 40347005739697^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911380383 10000000000 40347005739697 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2911380511/5000000000 : ℝ)^4727 ≤ (50139440371767/100000000000000 : ℝ)^3703 := by
    have hnat : (2911380511 : ℕ)^4727*100000000000000^3703 ≤ 50139440371767^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2911380511 5000000000 50139440371767 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1583661/10000000 : ℝ), (4911380383/10000000000 : ℝ), (2911380511/5000000000 : ℝ)] ![(4756776939151/50000000000000 : ℝ), (40347005739697/100000000000000 : ℝ), (50139440371767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1583661/10000000 : ℝ)|^4727 ≤ (4756776939151/50000000000000 : ℝ)^3703
        have hw : |(-1583661/10000000 : ℝ)|=(1583661/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4911380383/10000000000 : ℝ)|^4727 ≤ (40347005739697/100000000000000 : ℝ)^3703
        have hw : |(4911380383/10000000000 : ℝ)|=(4911380383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2911380511/5000000000 : ℝ)|^4727 ≤ (50139440371767/100000000000000 : ℝ)^3703
        have hw : |(2911380511/5000000000 : ℝ)|=(2911380511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s0_5 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (324657871/625000000 : ℝ)*x 0 + (-1178049233/10000000000 : ℝ)*x 1 + (2911380651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (324657871/625000000 : ℝ)^4727 ≤ (43339621001227/100000000000000 : ℝ)^3703 := by
    have hnat : (324657871 : ℕ)^4727*100000000000000^3703 ≤ 43339621001227^3703*625000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324657871 625000000 43339621001227 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178049233/10000000000 : ℝ)^4727 ≤ (6520935534259/100000000000000 : ℝ)^3703 := by
    have hnat : (1178049233 : ℕ)^4727*100000000000000^3703 ≤ 6520935534259^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178049233 10000000000 6520935534259 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2911380651/5000000000 : ℝ)^4727 ≤ (50139443449567/100000000000000 : ℝ)^3703 := by
    have hnat : (2911380651 : ℕ)^4727*100000000000000^3703 ≤ 50139443449567^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2911380651 5000000000 50139443449567 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(324657871/625000000 : ℝ), (-1178049233/10000000000 : ℝ), (2911380651/5000000000 : ℝ)] ![(43339621001227/100000000000000 : ℝ), (6520935534259/100000000000000 : ℝ), (50139443449567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(324657871/625000000 : ℝ)|^4727 ≤ (43339621001227/100000000000000 : ℝ)^3703
        have hw : |(324657871/625000000 : ℝ)|=(324657871/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1178049233/10000000000 : ℝ)|^4727 ≤ (6520935534259/100000000000000 : ℝ)^3703
        have hw : |(-1178049233/10000000000 : ℝ)|=(1178049233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2911380651/5000000000 : ℝ)|^4727 ≤ (50139443449567/100000000000000 : ℝ)^3703
        have hw : |(2911380651/5000000000 : ℝ)|=(2911380651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s0_6 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259726301/500000000 : ℝ)*x 0 + (1164552209/2000000000 : ℝ)*x 1 + (-1178049507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259726301/500000000 : ℝ)^4727 ≤ (43339621895871/100000000000000 : ℝ)^3703 := by
    have hnat : (259726301 : ℕ)^4727*100000000000000^3703 ≤ 43339621895871^3703*500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259726301 500000000 43339621895871 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1164552209/2000000000 : ℝ)^4727 ≤ (25069720312293/50000000000000 : ℝ)^3703 := by
    have hnat : (1164552209 : ℕ)^4727*50000000000000^3703 ≤ 25069720312293^3703*2000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164552209 2000000000 25069720312293 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1178049507/10000000000 : ℝ)^4727 ≤ (1630234367591/25000000000000 : ℝ)^3703 := by
    have hnat : (1178049507 : ℕ)^4727*25000000000000^3703 ≤ 1630234367591^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178049507 10000000000 1630234367591 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259726301/500000000 : ℝ), (1164552209/2000000000 : ℝ), (-1178049507/10000000000 : ℝ)] ![(43339621895871/100000000000000 : ℝ), (25069720312293/50000000000000 : ℝ), (1630234367591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259726301/500000000 : ℝ)|^4727 ≤ (43339621895871/100000000000000 : ℝ)^3703
        have hw : |(259726301/500000000 : ℝ)|=(259726301/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1164552209/2000000000 : ℝ)|^4727 ≤ (25069720312293/50000000000000 : ℝ)^3703
        have hw : |(1164552209/2000000000 : ℝ)|=(1164552209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1178049507/10000000000 : ℝ)|^4727 ≤ (1630234367591/25000000000000 : ℝ)^3703
        have hw : |(-1178049507/10000000000 : ℝ)|=(1178049507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s0_7 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4120788603/10000000000 : ℝ)*x 0 + (5350554667/10000000000 : ℝ)*x 1 + (626910633/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4120788603/10000000000 : ℝ)^4727 ≤ (6449705209847/20000000000000 : ℝ)^3703 := by
    have hnat : (4120788603 : ℕ)^4727*20000000000000^3703 ≤ 6449705209847^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4120788603 10000000000 6449705209847 20000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5350554667/10000000000 : ℝ)^4727 ≤ (45008261403581/100000000000000 : ℝ)^3703 := by
    have hnat : (5350554667 : ℕ)^4727*100000000000000^3703 ≤ 45008261403581^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350554667 10000000000 45008261403581 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (626910633/2000000000 : ℝ)^4727 ≤ (1137160626563/5000000000000 : ℝ)^3703 := by
    have hnat : (626910633 : ℕ)^4727*5000000000000^3703 ≤ 1137160626563^3703*2000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626910633 2000000000 1137160626563 5000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4120788603/10000000000 : ℝ), (5350554667/10000000000 : ℝ), (626910633/2000000000 : ℝ)] ![(6449705209847/20000000000000 : ℝ), (45008261403581/100000000000000 : ℝ), (1137160626563/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4120788603/10000000000 : ℝ)|^4727 ≤ (6449705209847/20000000000000 : ℝ)^3703
        have hw : |(4120788603/10000000000 : ℝ)|=(4120788603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5350554667/10000000000 : ℝ)|^4727 ≤ (45008261403581/100000000000000 : ℝ)^3703
        have hw : |(5350554667/10000000000 : ℝ)|=(5350554667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(626910633/2000000000 : ℝ)|^4727 ≤ (1137160626563/5000000000000 : ℝ)^3703
        have hw : |(626910633/2000000000 : ℝ)|=(626910633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1602_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1923/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6107/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4723/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4723 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4723*1^1024 ≤ 0^1024*1^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4723/1024 : ℝ) ≤ (146076189902539123/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4723 ≤ (146076189902539123/10000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4723*10000000000000000000^1024 ≤ 146076189902539123^1024*5^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 146076189902539123 10000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (146076189902539123/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4723 := by
      have hnat : (1 : ℕ)^1024*1^4723 ≤ 1^4723*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10146076189902539123/10000000000000000000 : ℝ) ≤ (10031491366711547/10000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (10146076189902539123/10000000000000000000 : ℝ)^1024 ≤ (10031491366711547/10000000000000000 : ℝ)^4723 := by
      have hnat : (10146076189902539123 : ℕ)^1024*10000000000000000^4723 ≤ 10031491366711547^4723*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10146076189902539123 10000000000000000000 10031491366711547 10000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10031491366711547/10000000000000000 : ℝ)) (X := (10146076189902539123/10000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5146076189902539123/5000000000000000000 : ℝ) ≤ (5031491366711547/5000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (5146076189902539123/5000000000000000000 : ℝ)^1024 ≤ (5031491366711547/5000000000000000 : ℝ)^4723 := by
      have hnat : (5146076189902539123 : ℕ)^1024*5000000000000000^4723 ≤ 5031491366711547^4723*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5146076189902539123 5000000000000000000 5031491366711547 5000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5031491366711547/5000000000000000 : ℝ)) (X := (5146076189902539123/5000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(31491366711547/4000000000000000 : ℝ)*(0 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(31491366711547/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(146076189902539123/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(31491366711547/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4723/1024 : ℝ) := by
    rw [show (1 : ℝ)+(31491366711547/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10031491366711547/10000000000000000 : ℝ) by norm_num, show 1+(146076189902539123/10000000000000000000 : ℝ)+(0 : ℝ)=(10146076189902539123/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(146076189902539123/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(31491366711547/4000000000000000 : ℝ)*(2/5 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(31491366711547/4000000000000000 : ℝ)*(2/5 : ℝ)=(5031491366711547/5000000000000000 : ℝ) by norm_num, show 1+2*(146076189902539123/10000000000000000000 : ℝ)=(5146076189902539123/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(31491366711547/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31491366711547/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(31491366711547/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31491366711547/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(31491366711547/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (31491366711547/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-79037849/500000000 : ℝ)*X 0 0+(5848050017/10000000000 : ℝ)*X 0 1+(305435181/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5457027163/10000000000 : ℝ)*X 1 0+(-1056924031/5000000000 : ℝ)*X 1 1+(1221740689/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((682128381/1250000000 : ℝ)*X 2 0+(4886962803/10000000000 : ℝ)*X 2 1+(-264231019/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1028431613/2500000000 : ℝ)*X 0 0+(3073064291/10000000000 : ℝ)*X 0 1+(1352481221/2500000000 : ℝ)*X 0 2+(1028431613/2500000000 : ℝ)*X 1 0+(3073064291/10000000000 : ℝ)*X 1 1+(1352481221/2500000000 : ℝ)*X 1 2+(1028431613/2500000000 : ℝ)*X 2 0+(3073064291/10000000000 : ℝ)*X 2 1+(1352481221/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1583661/10000000 : ℝ)*X 0 0+(4911380383/10000000000 : ℝ)*X 0 1+(2911380511/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((324657871/625000000 : ℝ)*X 1 0+(-1178049233/10000000000 : ℝ)*X 1 1+(2911380651/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((259726301/500000000 : ℝ)*X 2 0+(1164552209/2000000000 : ℝ)*X 2 1+(-1178049507/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4120788603/10000000000 : ℝ)*X 0 0+(5350554667/10000000000 : ℝ)*X 0 1+(626910633/2000000000 : ℝ)*X 0 2+(4120788603/10000000000 : ℝ)*X 1 0+(5350554667/10000000000 : ℝ)*X 1 1+(626910633/2000000000 : ℝ)*X 1 2+(4120788603/10000000000 : ℝ)*X 2 0+(5350554667/10000000000 : ℝ)*X 2 1+(626910633/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (205230500110046639009439/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12496623/20000000000000 : ℝ)*(base1) + (1638254853/100000000000000 : ℝ)*(base19) + (1616327649/100000000000000 : ℝ)*(base23) + (116349393/50000000000000 : ℝ)*(upper3) + (99415491/50000000000000 : ℝ)*(upper5) + (367107556689121/50000000000000 : ℝ)*(major0) + (367107556689121/50000000000000 : ℝ)*(major1) + (367107556689121/50000000000000 : ℝ)*(major2) + (130061794865609/12500000000000 : ℝ)*(sp0) + (520249320362269/50000000000000 : ℝ)*(sp1) + (520249331325871/50000000000000 : ℝ)*(sp2) + (26745435382713/6250000000000 : ℝ)*(sp3) + (1196507527/20000000000000 : ℝ)*(sp4) + (2645529897/100000000000000 : ℝ)*(sp7) + (21396483706821/5000000000000 : ℝ)*(f.failure) + (1040500278979391/100000000000000 : ℝ)*(f.sum) + (183467685280187/100000000000000000000000000000 : ℝ)*base65 + (422719251219813/200000000000000000000000000000 : ℝ)*base68 + (470434568180187/200000000000000000000000000000 : ℝ)*base69 + (797073159780187/200000000000000000000000000000 : ℝ)*base71 + (140442992880187/100000000000000000000000000000 : ℝ)*base73 + (13504321019813/200000000000000000000000000000 : ℝ)*base76 + (470734775380187/200000000000000000000000000000 : ℝ)*base77 + (457757589380187/200000000000000000000000000000 : ℝ)*base79 + (593140970680187/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2953441/500000000000000000000 : ℝ)*base90 + (2953441/500000000000000000000 : ℝ)*base92 + (2953441/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98644919548864561618959/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1664997977/100000000000000 : ℝ)*(base19) + (851187097/50000000000000 : ℝ)*(base23) + (100640363/50000000000000 : ℝ)*(base32) + (59788679/20000000000000 : ℝ)*(upper3) + (22801753/20000000000000 : ℝ)*(upper5) + (193562279765401/25000000000000 : ℝ)*(major0) + (193562279765401/25000000000000 : ℝ)*(major1) + (193562279765401/25000000000000 : ℝ)*(major2) + (4566031673/100000000000000 : ℝ)*(sp1) + (4954544599/100000000000000 : ℝ)*(sp2) + (109723489537677/10000000000000 : ℝ)*(sp4) + (13715358304339/1250000000000 : ℝ)*(sp5) + (1097228238457977/100000000000000 : ℝ)*(sp6) + (45126287841259/10000000000000 : ℝ)*(sp7) + (112815769923329/25000000000000 : ℝ)*(f.failure) + (109723489537677/10000000000000 : ℝ)*(f.sum) + (64070909285347/50000000000000000000000000000 : ℝ)*base65 + (41711953785347/100000000000000000000000000000 : ℝ)*base67 + (444447368785347/100000000000000000000000000000 : ℝ)*base69 + (266486981114653/100000000000000000000000000000 : ℝ)*base72 + (55876455585347/50000000000000000000000000000 : ℝ)*base73 + (270621159985347/100000000000000000000000000000 : ℝ)*base75 + (389299291585347/100000000000000000000000000000 : ℝ)*base77 + (447363451414653/100000000000000000000000000000 : ℝ)*base80 + (230630549635347/50000000000000000000000000000 : ℝ)*base81 + (3209709/2500000000000000000000 : ℝ)*base90 + (3209709/2500000000000000000000 : ℝ)*base92 + (3209709/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1602_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1923/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6107/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1602_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1602_s1_0 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1707908787/10000000000 : ℝ)*x 0 + (5537579823/10000000000 : ℝ)*x 1 + (2557636799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1707908787/10000000000 : ℝ)^4727 ≤ (10476499063199/100000000000000 : ℝ)^3703 := by
    have hnat : (1707908787 : ℕ)^4727*100000000000000^3703 ≤ 10476499063199^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707908787 10000000000 10476499063199 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5537579823/10000000000 : ℝ)^4727 ≤ (23513085933173/50000000000000 : ℝ)^3703 := by
    have hnat : (5537579823 : ℕ)^4727*50000000000000^3703 ≤ 23513085933173^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537579823 10000000000 23513085933173 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2557636799/5000000000 : ℝ)^4727 ≤ (5312166132583/12500000000000 : ℝ)^3703 := by
    have hnat : (2557636799 : ℕ)^4727*12500000000000^3703 ≤ 5312166132583^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2557636799 5000000000 5312166132583 12500000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1707908787/10000000000 : ℝ), (5537579823/10000000000 : ℝ), (2557636799/5000000000 : ℝ)] ![(10476499063199/100000000000000 : ℝ), (23513085933173/50000000000000 : ℝ), (5312166132583/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1707908787/10000000000 : ℝ)|^4727 ≤ (10476499063199/100000000000000 : ℝ)^3703
        have hw : |(-1707908787/10000000000 : ℝ)|=(1707908787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5537579823/10000000000 : ℝ)|^4727 ≤ (23513085933173/50000000000000 : ℝ)^3703
        have hw : |(5537579823/10000000000 : ℝ)|=(5537579823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2557636799/5000000000 : ℝ)|^4727 ≤ (5312166132583/12500000000000 : ℝ)^3703
        have hw : |(2557636799/5000000000 : ℝ)|=(2557636799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s1_1 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374380769/10000000000 : ℝ)*x 0 + (-482268781/2500000000 : ℝ)*x 1 + (1023054691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374380769/10000000000 : ℝ)^4727 ≤ (4526426457511/10000000000000 : ℝ)^3703 := by
    have hnat : (5374380769 : ℕ)^4727*10000000000000^3703 ≤ 4526426457511^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374380769 10000000000 4526426457511 10000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482268781/2500000000 : ℝ)^4727 ≤ (1529800982611/12500000000000 : ℝ)^3703 := by
    have hnat : (482268781 : ℕ)^4727*12500000000000^3703 ≤ 1529800982611^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482268781 2500000000 1529800982611 12500000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023054691/2000000000 : ℝ)^4727 ≤ (424973275441/1000000000000 : ℝ)^3703 := by
    have hnat : (1023054691 : ℕ)^4727*1000000000000^3703 ≤ 424973275441^3703*2000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023054691 2000000000 424973275441 1000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374380769/10000000000 : ℝ), (-482268781/2500000000 : ℝ), (1023054691/2000000000 : ℝ)] ![(4526426457511/10000000000000 : ℝ), (1529800982611/12500000000000 : ℝ), (424973275441/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374380769/10000000000 : ℝ)|^4727 ≤ (4526426457511/10000000000000 : ℝ)^3703
        have hw : |(5374380769/10000000000 : ℝ)|=(5374380769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-482268781/2500000000 : ℝ)|^4727 ≤ (1529800982611/12500000000000 : ℝ)^3703
        have hw : |(-482268781/2500000000 : ℝ)|=(482268781/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023054691/2000000000 : ℝ)|^4727 ≤ (424973275441/1000000000000 : ℝ)^3703
        have hw : |(1023054691/2000000000 : ℝ)|=(1023054691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s1_2 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537438039/1000000000 : ℝ)*x 0 + (639409223/1250000000 : ℝ)*x 1 + (-964537599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537438039/1000000000 : ℝ)^4727 ≤ (45264260500387/100000000000000 : ℝ)^3703 := by
    have hnat : (537438039 : ℕ)^4727*100000000000000^3703 ≤ 45264260500387^3703*1000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537438039 1000000000 45264260500387 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (639409223/1250000000 : ℝ)^4727 ≤ (42497331033257/100000000000000 : ℝ)^3703 := by
    have hnat : (639409223 : ℕ)^4727*100000000000000^3703 ≤ 42497331033257^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      639409223 1250000000 42497331033257 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (964537599/5000000000 : ℝ)^4727 ≤ (6119204230091/50000000000000 : ℝ)^3703 := by
    have hnat : (964537599 : ℕ)^4727*50000000000000^3703 ≤ 6119204230091^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      964537599 5000000000 6119204230091 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537438039/1000000000 : ℝ), (639409223/1250000000 : ℝ), (-964537599/5000000000 : ℝ)] ![(45264260500387/100000000000000 : ℝ), (42497331033257/100000000000000 : ℝ), (6119204230091/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537438039/1000000000 : ℝ)|^4727 ≤ (45264260500387/100000000000000 : ℝ)^3703
        have hw : |(537438039/1000000000 : ℝ)|=(537438039/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(639409223/1250000000 : ℝ)|^4727 ≤ (42497331033257/100000000000000 : ℝ)^3703
        have hw : |(639409223/1250000000 : ℝ)|=(639409223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-964537599/5000000000 : ℝ)|^4727 ≤ (6119204230091/50000000000000 : ℝ)^3703
        have hw : |(-964537599/5000000000 : ℝ)|=(964537599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s1_3 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4206999411/10000000000 : ℝ)*x 0 + (371793347/1000000000 : ℝ)*x 1 + (948952161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4206999411/10000000000 : ℝ)^4727 ≤ (33112242774509/100000000000000 : ℝ)^3703 := by
    have hnat : (4206999411 : ℕ)^4727*100000000000000^3703 ≤ 33112242774509^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4206999411 10000000000 33112242774509 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (371793347/1000000000 : ℝ)^4727 ≤ (7069945014761/25000000000000 : ℝ)^3703 := by
    have hnat : (371793347 : ℕ)^4727*25000000000000^3703 ≤ 7069945014761^3703*1000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      371793347 1000000000 7069945014761 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948952161/2000000000 : ℝ)^4727 ≤ (38607977150777/100000000000000 : ℝ)^3703 := by
    have hnat : (948952161 : ℕ)^4727*100000000000000^3703 ≤ 38607977150777^3703*2000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948952161 2000000000 38607977150777 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4206999411/10000000000 : ℝ), (371793347/1000000000 : ℝ), (948952161/2000000000 : ℝ)] ![(33112242774509/100000000000000 : ℝ), (7069945014761/25000000000000 : ℝ), (38607977150777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4206999411/10000000000 : ℝ)|^4727 ≤ (33112242774509/100000000000000 : ℝ)^3703
        have hw : |(4206999411/10000000000 : ℝ)|=(4206999411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(371793347/1000000000 : ℝ)|^4727 ≤ (7069945014761/25000000000000 : ℝ)^3703
        have hw : |(371793347/1000000000 : ℝ)|=(371793347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(948952161/2000000000 : ℝ)|^4727 ≤ (38607977150777/100000000000000 : ℝ)^3703
        have hw : |(948952161/2000000000 : ℝ)|=(948952161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s1_4 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1708149193/10000000000 : ℝ)*x 0 + (127998523/250000000 : ℝ)*x 1 + (5532838979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1708149193/10000000000 : ℝ)^4727 ≤ (5239190786293/50000000000000 : ℝ)^3703 := by
    have hnat : (1708149193 : ℕ)^4727*50000000000000^3703 ≤ 5239190786293^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708149193 10000000000 5239190786293 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127998523/250000000 : ℝ)^4727 ≤ (1329588557741/3125000000000 : ℝ)^3703 := by
    have hnat : (127998523 : ℕ)^4727*3125000000000^3703 ≤ 1329588557741^3703*250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127998523 250000000 1329588557741 3125000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5532838979/10000000000 : ℝ)^4727 ≤ (46974784571021/100000000000000 : ℝ)^3703 := by
    have hnat : (5532838979 : ℕ)^4727*100000000000000^3703 ≤ 46974784571021^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5532838979 10000000000 46974784571021 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1708149193/10000000000 : ℝ), (127998523/250000000 : ℝ), (5532838979/10000000000 : ℝ)] ![(5239190786293/50000000000000 : ℝ), (1329588557741/3125000000000 : ℝ), (46974784571021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1708149193/10000000000 : ℝ)|^4727 ≤ (5239190786293/50000000000000 : ℝ)^3703
        have hw : |(-1708149193/10000000000 : ℝ)|=(1708149193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(127998523/250000000 : ℝ)|^4727 ≤ (1329588557741/3125000000000 : ℝ)^3703
        have hw : |(127998523/250000000 : ℝ)|=(127998523/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5532838979/10000000000 : ℝ)|^4727 ≤ (46974784571021/100000000000000 : ℝ)^3703
        have hw : |(5532838979/10000000000 : ℝ)|=(5532838979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s1_5 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5262176659/10000000000 : ℝ)*x 0 + (-188938687/1250000000 : ℝ)*x 1 + (1383209819/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5262176659/10000000000 : ℝ)^4727 ≤ (4406143020933/10000000000000 : ℝ)^3703 := by
    have hnat : (5262176659 : ℕ)^4727*10000000000000^3703 ≤ 4406143020933^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262176659 10000000000 4406143020933 10000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188938687/1250000000 : ℝ)^4727 ≤ (8963781988017/100000000000000 : ℝ)^3703 := by
    have hnat : (188938687 : ℕ)^4727*100000000000000^3703 ≤ 8963781988017^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188938687 1250000000 8963781988017 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1383209819/2500000000 : ℝ)^4727 ≤ (2935924236869/6250000000000 : ℝ)^3703 := by
    have hnat : (1383209819 : ℕ)^4727*6250000000000^3703 ≤ 2935924236869^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383209819 2500000000 2935924236869 6250000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5262176659/10000000000 : ℝ), (-188938687/1250000000 : ℝ), (1383209819/2500000000 : ℝ)] ![(4406143020933/10000000000000 : ℝ), (8963781988017/100000000000000 : ℝ), (2935924236869/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5262176659/10000000000 : ℝ)|^4727 ≤ (4406143020933/10000000000000 : ℝ)^3703
        have hw : |(5262176659/10000000000 : ℝ)|=(5262176659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188938687/1250000000 : ℝ)|^4727 ≤ (8963781988017/100000000000000 : ℝ)^3703
        have hw : |(-188938687/1250000000 : ℝ)|=(188938687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1383209819/2500000000 : ℝ)|^4727 ≤ (2935924236869/6250000000000 : ℝ)^3703
        have hw : |(1383209819/2500000000 : ℝ)|=(1383209819/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s1_6 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2631088041/5000000000 : ℝ)*x 0 + (553283949/1000000000 : ℝ)*x 1 + (-1511510003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2631088041/5000000000 : ℝ)^4727 ≤ (11015356010487/25000000000000 : ℝ)^3703 := by
    have hnat : (2631088041 : ℕ)^4727*25000000000000^3703 ≤ 11015356010487^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631088041 5000000000 11015356010487 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553283949/1000000000 : ℝ)^4727 ≤ (46974790109233/100000000000000 : ℝ)^3703 := by
    have hnat : (553283949 : ℕ)^4727*100000000000000^3703 ≤ 46974790109233^3703*1000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553283949 1000000000 46974790109233 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1511510003/10000000000 : ℝ)^4727 ≤ (8963785826153/100000000000000 : ℝ)^3703 := by
    have hnat : (1511510003 : ℕ)^4727*100000000000000^3703 ≤ 8963785826153^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511510003 10000000000 8963785826153 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2631088041/5000000000 : ℝ), (553283949/1000000000 : ℝ), (-1511510003/10000000000 : ℝ)] ![(11015356010487/25000000000000 : ℝ), (46974790109233/100000000000000 : ℝ), (8963785826153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2631088041/5000000000 : ℝ)|^4727 ≤ (11015356010487/25000000000000 : ℝ)^3703
        have hw : |(2631088041/5000000000 : ℝ)|=(2631088041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553283949/1000000000 : ℝ)|^4727 ≤ (46974790109233/100000000000000 : ℝ)^3703
        have hw : |(553283949/1000000000 : ℝ)|=(553283949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1511510003/10000000000 : ℝ)|^4727 ≤ (8963785826153/100000000000000 : ℝ)^3703
        have hw : |(-1511510003/10000000000 : ℝ)|=(1511510003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s1_7 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4207583081/10000000000 : ℝ)*x 0 + (2366706641/5000000000 : ℝ)*x 1 + (149178389/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4207583081/10000000000 : ℝ)^4727 ≤ (6623621435317/20000000000000 : ℝ)^3703 := by
    have hnat : (4207583081 : ℕ)^4727*20000000000000^3703 ≤ 6623621435317^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4207583081 10000000000 6623621435317 20000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2366706641/5000000000 : ℝ)^4727 ≤ (19245074105701/50000000000000 : ℝ)^3703 := by
    have hnat : (2366706641 : ℕ)^4727*50000000000000^3703 ≤ 19245074105701^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366706641 5000000000 19245074105701 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149178389/400000000 : ℝ)^4727 ≤ (28391744601219/100000000000000 : ℝ)^3703 := by
    have hnat : (149178389 : ℕ)^4727*100000000000000^3703 ≤ 28391744601219^3703*400000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149178389 400000000 28391744601219 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4207583081/10000000000 : ℝ), (2366706641/5000000000 : ℝ), (149178389/400000000 : ℝ)] ![(6623621435317/20000000000000 : ℝ), (19245074105701/50000000000000 : ℝ), (28391744601219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4207583081/10000000000 : ℝ)|^4727 ≤ (6623621435317/20000000000000 : ℝ)^3703
        have hw : |(4207583081/10000000000 : ℝ)|=(4207583081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2366706641/5000000000 : ℝ)|^4727 ≤ (19245074105701/50000000000000 : ℝ)^3703
        have hw : |(2366706641/5000000000 : ℝ)|=(2366706641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149178389/400000000 : ℝ)|^4727 ≤ (28391744601219/100000000000000 : ℝ)^3703
        have hw : |(149178389/400000000 : ℝ)|=(149178389/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1602_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6107/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1923/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8983/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17929/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6107/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1923/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6107/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1923/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6107/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1923/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6107/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1923/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6107/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1923/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6107/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1923/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1923/50000 : ℝ) ^ (4723/1024 : ℝ) ≤ (14879956899637/50000000000000000000 : ℝ) := by
    have hpowers : (1923/50000 : ℝ)^4723 ≤ (14879956899637/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1923 : ℕ)^4723*50000000000000000000^1024 ≤ 14879956899637^1024*50000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1923 50000 14879956899637 50000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1923/50000 : ℝ)) (X := (14879956899637/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (6107/25000 : ℝ) ^ (4723/1024 : ℝ) ≤ (150228573747374557/100000000000000000000 : ℝ) := by
    have hpowers : (6107/25000 : ℝ)^4723 ≤ (150228573747374557/100000000000000000000 : ℝ)^1024 := by
      have hnat : (6107 : ℕ)^4723*100000000000000000000^1024 ≤ 150228573747374557^1024*25000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6107 25000 150228573747374557 100000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6107/25000 : ℝ)) (X := (150228573747374557/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000014879956899637/25000000000000000000 : ℝ) ≤ (10000001290457109/10000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (25000014879956899637/25000000000000000000 : ℝ)^1024 ≤ (10000001290457109/10000000000000000 : ℝ)^4723 := by
      have hnat : (25000014879956899637 : ℕ)^1024*10000000000000000^4723 ≤ 10000001290457109^4723*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000014879956899637 25000000000000000000 10000001290457109 10000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001290457109/10000000000000000 : ℝ)) (X := (25000014879956899637/25000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100150258333661173831/100000000000000000000 : ℝ) ≤ (5001627928012637/5000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (100150258333661173831/100000000000000000000 : ℝ)^1024 ≤ (5001627928012637/5000000000000000 : ℝ)^4723 := by
      have hnat : (100150258333661173831 : ℕ)^1024*5000000000000000^4723 ≤ 5001627928012637^4723*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100150258333661173831 100000000000000000000 5001627928012637 5000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001627928012637/5000000000000000 : ℝ)) (X := (100150258333661173831/100000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50150228573747374557/50000000000000000000 : ℝ) ≤ (10006510421593439/10000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (50150228573747374557/50000000000000000000 : ℝ)^1024 ≤ (10006510421593439/10000000000000000 : ℝ)^4723 := by
      have hnat : (50150228573747374557 : ℕ)^1024*10000000000000000^4723 ≤ 10006510421593439^4723*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50150228573747374557 50000000000000000000 10006510421593439 10000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006510421593439/10000000000000000 : ℝ)) (X := (50150228573747374557/50000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14879956899637/50000000000000000000 : ℝ) ≤ ((102897496220918946129/102910000000000000000 : ℝ)+2*(650913113633/411640000000000 : ℝ)*(1923/50000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (102897496220918946129/102910000000000000000 : ℝ)+2*(650913113633/411640000000000 : ℝ)*(1923/50000 : ℝ)=(10000001290457109/10000000000000000 : ℝ) by norm_num, show 1+2*(14879956899637/50000000000000000000 : ℝ)=(25000014879956899637/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(150228573747374557/100000000000000000000 : ℝ)+(14879956899637/50000000000000000000 : ℝ) ≤ ((102897496220918946129/102910000000000000000 : ℝ)+(650913113633/411640000000000 : ℝ)*((6107/25000 : ℝ)+(1923/50000 : ℝ)))^(4723/1024 : ℝ) := by
    rw [show (102897496220918946129/102910000000000000000 : ℝ)+(650913113633/411640000000000 : ℝ)*((6107/25000 : ℝ)+(1923/50000 : ℝ))=(5001627928012637/5000000000000000 : ℝ) by norm_num, show 1+(150228573747374557/100000000000000000000 : ℝ)+(14879956899637/50000000000000000000 : ℝ)=(100150258333661173831/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(150228573747374557/100000000000000000000 : ℝ) ≤ ((102897496220918946129/102910000000000000000 : ℝ)+2*(650913113633/411640000000000 : ℝ)*(6107/25000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (102897496220918946129/102910000000000000000 : ℝ)+2*(650913113633/411640000000000 : ℝ)*(6107/25000 : ℝ)=(10006510421593439/10000000000000000 : ℝ) by norm_num, show 1+2*(150228573747374557/100000000000000000000 : ℝ)=(50150228573747374557/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (102897496220918946129/102910000000000000000 : ℝ)*(X 1 0+X 2 0)+(650913113633/411640000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (1923/50000 : ℝ)) (hi := (6107/25000 : ℝ)) (c := (102897496220918946129/102910000000000000000 : ℝ)) (alpha := (650913113633/411640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (102897496220918946129/102910000000000000000 : ℝ)*(X 0 1+X 2 1)+(650913113633/411640000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (1923/50000 : ℝ)) (hi := (6107/25000 : ℝ)) (c := (102897496220918946129/102910000000000000000 : ℝ)) (alpha := (650913113633/411640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (102897496220918946129/102910000000000000000 : ℝ)*(X 0 2+X 1 2)+(650913113633/411640000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (1923/50000 : ℝ)) (hi := (6107/25000 : ℝ)) (c := (102897496220918946129/102910000000000000000 : ℝ)) (alpha := (650913113633/411640000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1707908787/10000000000 : ℝ)*X 0 0+(5537579823/10000000000 : ℝ)*X 0 1+(2557636799/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5374380769/10000000000 : ℝ)*X 1 0+(-482268781/2500000000 : ℝ)*X 1 1+(1023054691/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((537438039/1000000000 : ℝ)*X 2 0+(639409223/1250000000 : ℝ)*X 2 1+(-964537599/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4206999411/10000000000 : ℝ)*X 0 0+(371793347/1000000000 : ℝ)*X 0 1+(948952161/2000000000 : ℝ)*X 0 2+(4206999411/10000000000 : ℝ)*X 1 0+(371793347/1000000000 : ℝ)*X 1 1+(948952161/2000000000 : ℝ)*X 1 2+(4206999411/10000000000 : ℝ)*X 2 0+(371793347/1000000000 : ℝ)*X 2 1+(948952161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1708149193/10000000000 : ℝ)*X 0 0+(127998523/250000000 : ℝ)*X 0 1+(5532838979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5262176659/10000000000 : ℝ)*X 1 0+(-188938687/1250000000 : ℝ)*X 1 1+(1383209819/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2631088041/5000000000 : ℝ)*X 2 0+(553283949/1000000000 : ℝ)*X 2 1+(-1511510003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4207583081/10000000000 : ℝ)*X 0 0+(2366706641/5000000000 : ℝ)*X 0 1+(149178389/400000000 : ℝ)*X 0 2+(4207583081/10000000000 : ℝ)*X 1 0+(2366706641/5000000000 : ℝ)*X 1 1+(149178389/400000000 : ℝ)*X 1 2+(4207583081/10000000000 : ℝ)*X 2 0+(2366706641/5000000000 : ℝ)*X 2 1+(149178389/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5803095012836196570713186127/643187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (100235303/100000000000000 : ℝ)*(base1) + (957862801/50000000000000 : ℝ)*(base19) + (174873633/10000000000000 : ℝ)*(base23) + (1487743/625000000000 : ℝ)*(upper3) + (167378157/100000000000000 : ℝ)*(upper5) + (1670933517779831/100000000000000 : ℝ)*(major0) + (1670933517779831/100000000000000 : ℝ)*(major1) + (208866689722479/12500000000000 : ℝ)*(major2) + (1183982935080143/50000000000000 : ℝ)*(sp0) + (591994631271703/25000000000000 : ℝ)*(sp1) + (591994673019021/25000000000000 : ℝ)*(sp2) + (97387970651729/10000000000000 : ℝ)*(sp3) + (14670887431/100000000000000 : ℝ)*(sp4) + (6487247979/100000000000000 : ℝ)*(sp7) + (243471573500143/25000000000000 : ℝ)*(f.failure) + (1183990220406207/50000000000000 : ℝ)*(f.sum) + (95460219352943/41164000000000000000000000000 : ℝ)*base65 + (3536200671469724199/10291000000000000000000000000000000 : ℝ)*base67 + (6787385414814302541/1286375000000000000000000000000000 : ℝ)*base69 + (25719082616938724199/10291000000000000000000000000000000 : ℝ)*base71 + (222555902550519/41164000000000000000000000000 : ℝ)*base73 + (7774969613120177541/1286375000000000000000000000000000 : ℝ)*base75 + (54397247812081525801/10291000000000000000000000000000000 : ℝ)*base78 + (25425849510716525801/10291000000000000000000000000000000 : ℝ)*base80 + (37674175712897/20582000000000000000000000000 : ℝ)*base81 + (16550397/2500000000000000000000 : ℝ)*base89 + (16550397/2500000000000000000000 : ℝ)*base91 + (8449603/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30548584858424603118130127877/2572750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (455524967/20000000000000 : ℝ)*(base19) + (200605027/10000000000000 : ℝ)*(base23) + (55517/500000000000 : ℝ)*(upper2) + (187178017/50000000000000 : ℝ)*(upper3) + (12658611/6250000000000 : ℝ)*(upper5) + (854491139525271/50000000000000 : ℝ)*(major0) + (854491139525271/50000000000000 : ℝ)*(major1) + (854491139525271/50000000000000 : ℝ)*(major2) + (8561836551/50000000000000 : ℝ)*(sp1) + (15852111509/100000000000000 : ℝ)*(sp2) + (1210950770945203/50000000000000 : ℝ)*(sp4) + (2421882140592469/100000000000000 : ℝ)*(sp5) + (605470920932157/25000000000000 : ℝ)*(sp6) + (996062620413893/100000000000000 : ℝ)*(sp7) + (996062620413893/100000000000000 : ℝ)*(f.failure) + (1210950770945203/50000000000000 : ℝ)*(f.sum) + (18509927502591/5145500000000000000000000000 : ℝ)*base66 + (6089586953774124041/5145500000000000000000000000000000 : ℝ)*base68 + (28380351393764375959/5145500000000000000000000000000000 : ℝ)*base69 + (2578725614057875959/5145500000000000000000000000000000 : ℝ)*base71 + (39356164947671/10291000000000000000000000000 : ℝ)*base74 + (10150101333525624041/5145500000000000000000000000000000 : ℝ)*base76 + (59521426271755624041/5145500000000000000000000000000000 : ℝ)*base78 + (19671063484022124041/5145500000000000000000000000000000 : ℝ)*base80 + (30004739379837/5145500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (33888353/10000000000000000000000 : ℝ)*base90 + (33888353/10000000000000000000000 : ℝ)*base92 + (33888353/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1602_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6107/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1923/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17929/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1602_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1602_s2_0 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-861477027/5000000000 : ℝ)*x 0 + (5470262861/10000000000 : ℝ)*x 1 + (5172756411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861477027/5000000000 : ℝ)^4727 ≤ (2648613140717/25000000000000 : ℝ)^3703 := by
    have hnat : (861477027 : ℕ)^4727*25000000000000^3703 ≤ 2648613140717^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861477027 5000000000 2648613140717 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470262861/10000000000 : ℝ)^4727 ≤ (46297648834251/100000000000000 : ℝ)^3703 := by
    have hnat : (5470262861 : ℕ)^4727*100000000000000^3703 ≤ 46297648834251^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470262861 10000000000 46297648834251 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172756411/10000000000 : ℝ)^4727 ≤ (21553949291603/50000000000000 : ℝ)^3703 := by
    have hnat : (5172756411 : ℕ)^4727*50000000000000^3703 ≤ 21553949291603^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172756411 10000000000 21553949291603 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-861477027/5000000000 : ℝ), (5470262861/10000000000 : ℝ), (5172756411/10000000000 : ℝ)] ![(2648613140717/25000000000000 : ℝ), (46297648834251/100000000000000 : ℝ), (21553949291603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-861477027/5000000000 : ℝ)|^4727 ≤ (2648613140717/25000000000000 : ℝ)^3703
        have hw : |(-861477027/5000000000 : ℝ)|=(861477027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470262861/10000000000 : ℝ)|^4727 ≤ (46297648834251/100000000000000 : ℝ)^3703
        have hw : |(5470262861/10000000000 : ℝ)|=(5470262861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172756411/10000000000 : ℝ)|^4727 ≤ (21553949291603/50000000000000 : ℝ)^3703
        have hw : |(5172756411/10000000000 : ℝ)|=(5172756411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s2_1 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5356902067/10000000000 : ℝ)*x 0 + (-938338929/5000000000 : ℝ)*x 1 + (5172756443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356902067/10000000000 : ℝ)^4727 ≤ (22538215631531/50000000000000 : ℝ)^3703 := by
    have hnat : (5356902067 : ℕ)^4727*50000000000000^3703 ≤ 22538215631531^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356902067 10000000000 22538215631531 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (938338929/5000000000 : ℝ)^4727 ≤ (590783489839/5000000000000 : ℝ)^3703 := by
    have hnat : (938338929 : ℕ)^4727*5000000000000^3703 ≤ 590783489839^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      938338929 5000000000 590783489839 5000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172756443/10000000000 : ℝ)^4727 ≤ (43107898923627/100000000000000 : ℝ)^3703 := by
    have hnat : (5172756443 : ℕ)^4727*100000000000000^3703 ≤ 43107898923627^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172756443 10000000000 43107898923627 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356902067/10000000000 : ℝ), (-938338929/5000000000 : ℝ), (5172756443/10000000000 : ℝ)] ![(22538215631531/50000000000000 : ℝ), (590783489839/5000000000000 : ℝ), (43107898923627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356902067/10000000000 : ℝ)|^4727 ≤ (22538215631531/50000000000000 : ℝ)^3703
        have hw : |(5356902067/10000000000 : ℝ)|=(5356902067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-938338929/5000000000 : ℝ)|^4727 ≤ (590783489839/5000000000000 : ℝ)^3703
        have hw : |(-938338929/5000000000 : ℝ)|=(938338929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172756443/10000000000 : ℝ)|^4727 ≤ (43107898923627/100000000000000 : ℝ)^3703
        have hw : |(5172756443/10000000000 : ℝ)|=(5172756443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s2_2 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678451049/5000000000 : ℝ)*x 0 + (5172756399/10000000000 : ℝ)*x 1 + (-15013423/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678451049/5000000000 : ℝ)^4727 ≤ (901528631921/2000000000000 : ℝ)^3703 := by
    have hnat : (2678451049 : ℕ)^4727*2000000000000^3703 ≤ 901528631921^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678451049 5000000000 901528631921 2000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5172756399/10000000000 : ℝ)^4727 ≤ (10776974613887/25000000000000 : ℝ)^3703 := by
    have hnat : (5172756399 : ℕ)^4727*25000000000000^3703 ≤ 10776974613887^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172756399 10000000000 10776974613887 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15013423/80000000 : ℝ)^4727 ≤ (11815669933411/100000000000000 : ℝ)^3703 := by
    have hnat : (15013423 : ℕ)^4727*100000000000000^3703 ≤ 11815669933411^3703*80000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15013423 80000000 11815669933411 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678451049/5000000000 : ℝ), (5172756399/10000000000 : ℝ), (-15013423/80000000 : ℝ)] ![(901528631921/2000000000000 : ℝ), (10776974613887/25000000000000 : ℝ), (11815669933411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678451049/5000000000 : ℝ)|^4727 ≤ (901528631921/2000000000000 : ℝ)^3703
        have hw : |(2678451049/5000000000 : ℝ)|=(2678451049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5172756399/10000000000 : ℝ)|^4727 ≤ (10776974613887/25000000000000 : ℝ)^3703
        have hw : |(5172756399/10000000000 : ℝ)|=(5172756399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15013423/80000000 : ℝ)|^4727 ≤ (11815669933411/100000000000000 : ℝ)^3703
        have hw : |(-15013423/80000000 : ℝ)|=(15013423/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s2_3 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84361539/200000000 : ℝ)*x 0 + (3868473029/10000000000 : ℝ)*x 1 + (57398159/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84361539/200000000 : ℝ)^4727 ≤ (16611791142771/50000000000000 : ℝ)^3703 := by
    have hnat : (84361539 : ℕ)^4727*50000000000000^3703 ≤ 16611791142771^3703*200000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84361539 200000000 16611791142771 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3868473029/10000000000 : ℝ)^4727 ≤ (7437395078181/25000000000000 : ℝ)^3703 := by
    have hnat : (3868473029 : ℕ)^4727*25000000000000^3703 ≤ 7437395078181^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3868473029 10000000000 7437395078181 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57398159/125000000 : ℝ)^4727 ≤ (37026837390933/100000000000000 : ℝ)^3703 := by
    have hnat : (57398159 : ℕ)^4727*100000000000000^3703 ≤ 37026837390933^3703*125000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57398159 125000000 37026837390933 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84361539/200000000 : ℝ), (3868473029/10000000000 : ℝ), (57398159/125000000 : ℝ)] ![(16611791142771/50000000000000 : ℝ), (7437395078181/25000000000000 : ℝ), (37026837390933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84361539/200000000 : ℝ)|^4727 ≤ (16611791142771/50000000000000 : ℝ)^3703
        have hw : |(84361539/200000000 : ℝ)|=(84361539/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3868473029/10000000000 : ℝ)|^4727 ≤ (7437395078181/25000000000000 : ℝ)^3703
        have hw : |(3868473029/10000000000 : ℝ)|=(3868473029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57398159/125000000 : ℝ)|^4727 ≤ (37026837390933/100000000000000 : ℝ)^3703
        have hw : |(57398159/125000000 : ℝ)|=(57398159/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s2_4 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-861519023/5000000000 : ℝ)*x 0 + (5175080503/10000000000 : ℝ)*x 1 + (683489141/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (861519023/5000000000 : ℝ)^4727 ≤ (5297555927251/50000000000000 : ℝ)^3703 := by
    have hnat : (861519023 : ℕ)^4727*50000000000000^3703 ≤ 5297555927251^3703*5000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861519023 5000000000 5297555927251 50000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175080503/10000000000 : ℝ)^4727 ≤ (43132624192731/100000000000000 : ℝ)^3703 := by
    have hnat : (5175080503 : ℕ)^4727*100000000000000^3703 ≤ 43132624192731^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175080503 10000000000 43132624192731 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683489141/1250000000 : ℝ)^4727 ≤ (11568065985123/25000000000000 : ℝ)^3703 := by
    have hnat : (683489141 : ℕ)^4727*25000000000000^3703 ≤ 11568065985123^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683489141 1250000000 11568065985123 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-861519023/5000000000 : ℝ), (5175080503/10000000000 : ℝ), (683489141/1250000000 : ℝ)] ![(5297555927251/50000000000000 : ℝ), (43132624192731/100000000000000 : ℝ), (11568065985123/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-861519023/5000000000 : ℝ)|^4727 ≤ (5297555927251/50000000000000 : ℝ)^3703
        have hw : |(-861519023/5000000000 : ℝ)|=(861519023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175080503/10000000000 : ℝ)|^4727 ≤ (43132624192731/100000000000000 : ℝ)^3703
        have hw : |(5175080503/10000000000 : ℝ)|=(5175080503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683489141/1250000000 : ℝ)|^4727 ≤ (11568065985123/25000000000000 : ℝ)^3703
        have hw : |(683489141/1250000000 : ℝ)|=(683489141/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s2_5 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659749477/1250000000 : ℝ)*x 0 + (-19769013/125000000 : ℝ)*x 1 + (5467913381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659749477/1250000000 : ℝ)^4727 ≤ (5528823341151/12500000000000 : ℝ)^3703 := by
    have hnat : (659749477 : ℕ)^4727*12500000000000^3703 ≤ 5528823341151^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659749477 1250000000 5528823341151 12500000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19769013/125000000 : ℝ)^4727 ≤ (379885863417/4000000000000 : ℝ)^3703 := by
    have hnat : (19769013 : ℕ)^4727*4000000000000^3703 ≤ 379885863417^3703*125000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19769013 125000000 379885863417 4000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467913381/10000000000 : ℝ)^4727 ≤ (46272266673567/100000000000000 : ℝ)^3703 := by
    have hnat : (5467913381 : ℕ)^4727*100000000000000^3703 ≤ 46272266673567^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467913381 10000000000 46272266673567 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659749477/1250000000 : ℝ), (-19769013/125000000 : ℝ), (5467913381/10000000000 : ℝ)] ![(5528823341151/12500000000000 : ℝ), (379885863417/4000000000000 : ℝ), (46272266673567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659749477/1250000000 : ℝ)|^4727 ≤ (5528823341151/12500000000000 : ℝ)^3703
        have hw : |(659749477/1250000000 : ℝ)|=(659749477/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19769013/125000000 : ℝ)|^4727 ≤ (379885863417/4000000000000 : ℝ)^3703
        have hw : |(-19769013/125000000 : ℝ)|=(19769013/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467913381/10000000000 : ℝ)|^4727 ≤ (46272266673567/100000000000000 : ℝ)^3703
        have hw : |(5467913381/10000000000 : ℝ)|=(5467913381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s2_6 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (659749481/1250000000 : ℝ)*x 0 + (5467913239/10000000000 : ℝ)*x 1 + (-395380299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (659749481/1250000000 : ℝ)^4727 ≤ (44230587071531/100000000000000 : ℝ)^3703 := by
    have hnat : (659749481 : ℕ)^4727*100000000000000^3703 ≤ 44230587071531^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      659749481 1250000000 44230587071531 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467913239/10000000000 : ℝ)^4727 ≤ (11568066284897/25000000000000 : ℝ)^3703 := by
    have hnat : (5467913239 : ℕ)^4727*25000000000000^3703 ≤ 11568066284897^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467913239 10000000000 11568066284897 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (395380299/2500000000 : ℝ)^4727 ≤ (9497147781269/100000000000000 : ℝ)^3703 := by
    have hnat : (395380299 : ℕ)^4727*100000000000000^3703 ≤ 9497147781269^3703*2500000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395380299 2500000000 9497147781269 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(659749481/1250000000 : ℝ), (5467913239/10000000000 : ℝ), (-395380299/2500000000 : ℝ)] ![(44230587071531/100000000000000 : ℝ), (11568066284897/25000000000000 : ℝ), (9497147781269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(659749481/1250000000 : ℝ)|^4727 ≤ (44230587071531/100000000000000 : ℝ)^3703
        have hw : |(659749481/1250000000 : ℝ)|=(659749481/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467913239/10000000000 : ℝ)|^4727 ≤ (11568066284897/25000000000000 : ℝ)^3703
        have hw : |(5467913239/10000000000 : ℝ)|=(5467913239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-395380299/2500000000 : ℝ)|^4727 ≤ (9497147781269/100000000000000 : ℝ)^3703
        have hw : |(-395380299/2500000000 : ℝ)|=(395380299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1602_s2_7 (p : ℝ) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4218281441/10000000000 : ℝ)*x 0 + (573275269/1250000000 : ℝ)*x 1 + (3874186289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4218281441/10000000000 : ℝ)^4727 ≤ (8306409592511/25000000000000 : ℝ)^3703 := by
    have hnat : (4218281441 : ℕ)^4727*25000000000000^3703 ≤ 8306409592511^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218281441 10000000000 8306409592511 25000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (573275269/1250000000 : ℝ)^4727 ≤ (2310542719037/6250000000000 : ℝ)^3703 := by
    have hnat : (573275269 : ℕ)^4727*6250000000000^3703 ≤ 2310542719037^3703*1250000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573275269 1250000000 2310542719037 6250000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3874186289/10000000000 : ℝ)^4727 ≤ (29805678107859/100000000000000 : ℝ)^3703 := by
    have hnat : (3874186289 : ℕ)^4727*100000000000000^3703 ≤ 29805678107859^3703*10000000000^4727 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3874186289 10000000000 29805678107859 100000000000000 4727 3703 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4727/1024 : ℝ)) 4727 3703 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4218281441/10000000000 : ℝ), (573275269/1250000000 : ℝ), (3874186289/10000000000 : ℝ)] ![(8306409592511/25000000000000 : ℝ), (2310542719037/6250000000000 : ℝ), (29805678107859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4218281441/10000000000 : ℝ)|^4727 ≤ (8306409592511/25000000000000 : ℝ)^3703
        have hw : |(4218281441/10000000000 : ℝ)|=(4218281441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(573275269/1250000000 : ℝ)|^4727 ≤ (2310542719037/6250000000000 : ℝ)^3703
        have hw : |(573275269/1250000000 : ℝ)|=(573275269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3874186289/10000000000 : ℝ)|^4727 ≤ (29805678107859/100000000000000 : ℝ)^3703
        have hw : |(3874186289/10000000000 : ℝ)|=(3874186289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1602_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17929/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (409/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16529/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17929/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8983/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17929/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8983/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17929/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8983/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17929/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8983/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17929/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8983/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17929/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8983/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8983/100000 : ℝ) ^ (4723/1024 : ℝ) ≤ (37222078832943/2500000000000000000 : ℝ) := by
    have hpowers : (8983/100000 : ℝ)^4723 ≤ (37222078832943/2500000000000000000 : ℝ)^1024 := by
      have hnat : (8983 : ℕ)^4723*2500000000000000000^1024 ≤ 37222078832943^1024*100000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8983 100000 37222078832943 2500000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8983/100000 : ℝ)) (X := (37222078832943/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17929/100000 : ℝ) ^ (4723/1024 : ℝ) ≤ (36072243162653977/100000000000000000000 : ℝ) := by
    have hpowers : (17929/100000 : ℝ)^4723 ≤ (36072243162653977/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17929 : ℕ)^4723*100000000000000000000^1024 ≤ 36072243162653977^1024*100000^4723 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17929 100000 36072243162653977 100000000000000000000 4723 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17929/100000 : ℝ)) (X := (36072243162653977/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250037222078832943/1250000000000000000 : ℝ) ≤ (1000006456060009/1000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (1250037222078832943/1250000000000000000 : ℝ)^1024 ≤ (1000006456060009/1000000000000000 : ℝ)^4723 := by
      have hnat : (1250037222078832943 : ℕ)^1024*1000000000000000^4723 ≤ 1000006456060009^4723*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250037222078832943 1250000000000000000 1000006456060009 1000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000006456060009/1000000000000000 : ℝ)) (X := (1250037222078832943/1250000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037561126315971697/100000000000000000000 : ℝ) ≤ (78131361313197/78125000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (100037561126315971697/100000000000000000000 : ℝ)^1024 ≤ (78131361313197/78125000000000 : ℝ)^4723 := by
      have hnat : (100037561126315971697 : ℕ)^1024*78125000000000^4723 ≤ 78131361313197^4723*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037561126315971697 100000000000000000000 78131361313197 78125000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78131361313197/78125000000000 : ℝ)) (X := (100037561126315971697/100000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036072243162653977/50000000000000000000 : ℝ) ≤ (5000781967789171/5000000000000000 : ℝ) ^ (4723/1024 : ℝ) := by
    have hpowers : (50036072243162653977/50000000000000000000 : ℝ)^1024 ≤ (5000781967789171/5000000000000000 : ℝ)^4723 := by
      have hnat : (50036072243162653977 : ℕ)^1024*5000000000000000^4723 ≤ 5000781967789171^4723*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036072243162653977 50000000000000000000 5000781967789171 5000000000000000 1024 4723 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000781967789171/5000000000000000 : ℝ)) (X := (50036072243162653977/50000000000000000000 : ℝ)) (by norm_num) 4723 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(37222078832943/2500000000000000000 : ℝ) ≤ ((1397611073026543241/1397812500000000000 : ℝ)+2*(374843744563/447300000000000 : ℝ)*(8983/100000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (1397611073026543241/1397812500000000000 : ℝ)+2*(374843744563/447300000000000 : ℝ)*(8983/100000 : ℝ)=(1000006456060009/1000000000000000 : ℝ) by norm_num, show 1+2*(37222078832943/2500000000000000000 : ℝ)=(1250037222078832943/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36072243162653977/100000000000000000000 : ℝ)+(37222078832943/2500000000000000000 : ℝ) ≤ ((1397611073026543241/1397812500000000000 : ℝ)+(374843744563/447300000000000 : ℝ)*((17929/100000 : ℝ)+(8983/100000 : ℝ)))^(4723/1024 : ℝ) := by
    rw [show (1397611073026543241/1397812500000000000 : ℝ)+(374843744563/447300000000000 : ℝ)*((17929/100000 : ℝ)+(8983/100000 : ℝ))=(78131361313197/78125000000000 : ℝ) by norm_num, show 1+(36072243162653977/100000000000000000000 : ℝ)+(37222078832943/2500000000000000000 : ℝ)=(100037561126315971697/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36072243162653977/100000000000000000000 : ℝ) ≤ ((1397611073026543241/1397812500000000000 : ℝ)+2*(374843744563/447300000000000 : ℝ)*(17929/100000 : ℝ))^(4723/1024 : ℝ) := by
    rw [show (1397611073026543241/1397812500000000000 : ℝ)+2*(374843744563/447300000000000 : ℝ)*(17929/100000 : ℝ)=(5000781967789171/5000000000000000 : ℝ) by norm_num, show 1+2*(36072243162653977/100000000000000000000 : ℝ)=(50036072243162653977/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1397611073026543241/1397812500000000000 : ℝ)*(X 1 0+X 2 0)+(374843744563/447300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (8983/100000 : ℝ)) (hi := (17929/100000 : ℝ)) (c := (1397611073026543241/1397812500000000000 : ℝ)) (alpha := (374843744563/447300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1397611073026543241/1397812500000000000 : ℝ)*(X 0 1+X 2 1)+(374843744563/447300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (8983/100000 : ℝ)) (hi := (17929/100000 : ℝ)) (c := (1397611073026543241/1397812500000000000 : ℝ)) (alpha := (374843744563/447300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1397611073026543241/1397812500000000000 : ℝ)*(X 0 2+X 1 2)+(374843744563/447300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4723/1024 : ℝ)) (lo := (8983/100000 : ℝ)) (hi := (17929/100000 : ℝ)) (c := (1397611073026543241/1397812500000000000 : ℝ)) (alpha := (374843744563/447300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-861477027/5000000000 : ℝ)*X 0 0+(5470262861/10000000000 : ℝ)*X 0 1+(5172756411/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356902067/10000000000 : ℝ)*X 1 0+(-938338929/5000000000 : ℝ)*X 1 1+(5172756443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2678451049/5000000000 : ℝ)*X 2 0+(5172756399/10000000000 : ℝ)*X 2 1+(-15013423/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((84361539/200000000 : ℝ)*X 0 0+(3868473029/10000000000 : ℝ)*X 0 1+(57398159/125000000 : ℝ)*X 0 2+(84361539/200000000 : ℝ)*X 1 0+(3868473029/10000000000 : ℝ)*X 1 1+(57398159/125000000 : ℝ)*X 1 2+(84361539/200000000 : ℝ)*X 2 0+(3868473029/10000000000 : ℝ)*X 2 1+(57398159/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-861519023/5000000000 : ℝ)*X 0 0+(5175080503/10000000000 : ℝ)*X 0 1+(683489141/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((659749477/1250000000 : ℝ)*X 1 0+(-19769013/125000000 : ℝ)*X 1 1+(5467913381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((659749481/1250000000 : ℝ)*X 2 0+(5467913239/10000000000 : ℝ)*X 2 1+(-395380299/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4218281441/10000000000 : ℝ)*X 0 0+(573275269/1250000000 : ℝ)*X 0 1+(3874186289/10000000000 : ℝ)*X 0 2+(4218281441/10000000000 : ℝ)*X 1 0+(573275269/1250000000 : ℝ)*X 1 1+(3874186289/10000000000 : ℝ)*X 1 2+(4218281441/10000000000 : ℝ)*X 2 0+(573275269/1250000000 : ℝ)*X 2 1+(3874186289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1602_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11820380334083179651215573/1941406250000000000000000000000 : ℝ) := by norm_num
    linear_combination (263394331/25000000000000 : ℝ)*(base19) + (505137351/50000000000000 : ℝ)*(base23) + (16808403/50000000000000 : ℝ)*(lower2) + (40272661/25000000000000 : ℝ)*(upper3) + (104415521/100000000000000 : ℝ)*(upper5) + (2371853430819639/100000000000000 : ℝ)*(major0) + (2371853430819639/100000000000000 : ℝ)*(major1) + (59296335770491/2500000000000 : ℝ)*(major2) + (210080269718133/6250000000000 : ℝ)*(sp0) + (3361295399632109/100000000000000 : ℝ)*(sp1) + (336129544293473/10000000000000 : ℝ)*(sp2) + (1382404704821191/100000000000000 : ℝ)*(sp3) + (1517214913/12500000000000 : ℝ)*(sp4) + (5500656441/100000000000000 : ℝ)*(sp7) + (5400039865147/390625000000 : ℝ)*(f.failure) + (420162056651179/12500000000000 : ℝ)*(f.sum) + (259563748724527/44730000000000000000000000000 : ℝ)*base65 + (140446426154208751/139781250000000000000000000000000 : ℝ)*base68 + (56014917125896789/3993750000000000000000000000000 : ℝ)*base69 + (341820756100822499/139781250000000000000000000000000 : ℝ)*base71 + (6626092181693/44730000000000000000000000000 : ℝ)*base74 + (20343964474809461/3993750000000000000000000000000 : ℝ)*base76 + (29234653469911493/7765625000000000000000000000000 : ℝ)*base77 + (2078780268505243/7765625000000000000000000000000 : ℝ)*base79 + (7388814986379/1242500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (151931/19531250000000000000 : ℝ)*base90 + (151931/19531250000000000000 : ℝ)*base92 + (694487/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (279206775011236060569673/32812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (517980513/50000000000000 : ℝ)*(base19) + (1232427971/100000000000000 : ℝ)*(base23) + (7276223/4000000000000 : ℝ)*(upper3) + (84918209/100000000000000 : ℝ)*(lower4) + (30854327/25000000000000 : ℝ)*(upper5) + (481938113460799/20000000000000 : ℝ)*(major0) + (481938113460799/20000000000000 : ℝ)*(major1) + (481938113460799/20000000000000 : ℝ)*(major2) + (12671169261/100000000000000 : ℝ)*(sp1) + (2733184659/20000000000000 : ℝ)*(sp2) + (3414917662393209/100000000000000 : ℝ)*(sp4) + (1707451977631461/50000000000000 : ℝ)*(sp5) + (426862845505243/12500000000000 : ℝ)*(sp6) + (1404463188576149/100000000000000 : ℝ)*(sp7) + (1404463188576149/100000000000000 : ℝ)*(f.failure) + (3414917662393209/100000000000000 : ℝ)*(f.sum) + (58382085719/31500000000000000000000000 : ℝ)*base66 + (685433411155327/196875000000000000000000000000 : ℝ)*base67 + (734417478674077/196875000000000000000000000000 : ℝ)*base69 + (124119739402619/24609375000000000000000000000 : ℝ)*base71 + (77260004743/63000000000000000000000000 : ℝ)*base74 + (133999458651101/98437500000000000000000000000 : ℝ)*base75 + (24634737057173/196875000000000000000000000000 : ℝ)*base78 + (1084041130163423/196875000000000000000000000000 : ℝ)*base80 + (33008449091/63000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13197071/10000000000000000000000 : ℝ)*base89 + (13197071/10000000000000000000000 : ℝ)*base91 + (13197071/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1602_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17929/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (409/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1602_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1602_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (409/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1602_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1602_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1602_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4723/1024 : ℝ) ≤ p) (hpb : p ≤ (4727/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (171573779/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (409/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16529/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1602_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
