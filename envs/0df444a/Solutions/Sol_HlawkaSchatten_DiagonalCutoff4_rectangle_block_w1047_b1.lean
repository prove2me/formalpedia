-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1047_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:52:02.020811+00:00
-- url     : https://prove2.me/submissions/2e4de7ba-ecfb-4c1a-914a-e9d93be871b8

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
theorem support_rectangle_w1047_s3_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-441630289/2000000000 : ℝ)*x 0 + (5439786659/10000000000 : ℝ)*x 1 + (2611135849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441630289/2000000000 : ℝ)^515 ≤ (13398828360221/100000000000000 : ℝ)^387 := by
    have hnat : (441630289 : ℕ)^515*100000000000000^387 ≤ 13398828360221^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441630289 2000000000 13398828360221 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439786659/10000000000 : ℝ)^515 ≤ (11119000500719/25000000000000 : ℝ)^387 := by
    have hnat : (5439786659 : ℕ)^515*25000000000000^387 ≤ 11119000500719^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439786659 10000000000 11119000500719 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611135849/5000000000 : ℝ)^515 ≤ (21062584813603/50000000000000 : ℝ)^387 := by
    have hnat : (2611135849 : ℕ)^515*50000000000000^387 ≤ 21062584813603^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611135849 5000000000 21062584813603 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441630289/2000000000 : ℝ), (5439786659/10000000000 : ℝ), (2611135849/5000000000 : ℝ)] ![(13398828360221/100000000000000 : ℝ), (11119000500719/25000000000000 : ℝ), (21062584813603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441630289/2000000000 : ℝ)|^515 ≤ (13398828360221/100000000000000 : ℝ)^387
        have hw : |(-441630289/2000000000 : ℝ)|=(441630289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439786659/10000000000 : ℝ)|^515 ≤ (11119000500719/25000000000000 : ℝ)^387
        have hw : |(5439786659/10000000000 : ℝ)|=(5439786659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611135849/5000000000 : ℝ)|^515 ≤ (21062584813603/50000000000000 : ℝ)^387
        have hw : |(2611135849/5000000000 : ℝ)|=(2611135849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s3_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (669523233/1250000000 : ℝ)*x 0 + (-2319590219/10000000000 : ℝ)*x 1 + (163195997/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669523233/1250000000 : ℝ)^515 ≤ (5446090196643/12500000000000 : ℝ)^387 := by
    have hnat : (669523233 : ℕ)^515*12500000000000^387 ≤ 5446090196643^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669523233 1250000000 5446090196643 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2319590219/10000000000 : ℝ)^515 ≤ (894131660609/6250000000000 : ℝ)^387 := by
    have hnat : (2319590219 : ℕ)^515*6250000000000^387 ≤ 894131660609^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2319590219 10000000000 894131660609 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (163195997/312500000 : ℝ)^515 ≤ (1316411619953/3125000000000 : ℝ)^387 := by
    have hnat : (163195997 : ℕ)^515*3125000000000^387 ≤ 1316411619953^387*312500000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163195997 312500000 1316411619953 3125000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669523233/1250000000 : ℝ), (-2319590219/10000000000 : ℝ), (163195997/312500000 : ℝ)] ![(5446090196643/12500000000000 : ℝ), (894131660609/6250000000000 : ℝ), (1316411619953/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669523233/1250000000 : ℝ)|^515 ≤ (5446090196643/12500000000000 : ℝ)^387
        have hw : |(669523233/1250000000 : ℝ)|=(669523233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2319590219/10000000000 : ℝ)|^515 ≤ (894131660609/6250000000000 : ℝ)^387
        have hw : |(-2319590219/10000000000 : ℝ)|=(2319590219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(163195997/312500000 : ℝ)|^515 ≤ (1316411619953/3125000000000 : ℝ)^387
        have hw : |(163195997/312500000 : ℝ)|=(163195997/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s3_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5356185919/10000000000 : ℝ)*x 0 + (2611136069/5000000000 : ℝ)*x 1 + (-28994873/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356185919/10000000000 : ℝ)^515 ≤ (21784361084251/50000000000000 : ℝ)^387 := by
    have hnat : (5356185919 : ℕ)^515*50000000000000^387 ≤ 21784361084251^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356185919 10000000000 21784361084251 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611136069/5000000000 : ℝ)^515 ≤ (42125174350349/100000000000000 : ℝ)^387 := by
    have hnat : (2611136069 : ℕ)^515*100000000000000^387 ≤ 42125174350349^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611136069 5000000000 42125174350349 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28994873/125000000 : ℝ)^515 ≤ (14306103459133/100000000000000 : ℝ)^387 := by
    have hnat : (28994873 : ℕ)^515*100000000000000^387 ≤ 14306103459133^387*125000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28994873 125000000 14306103459133 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356185919/10000000000 : ℝ), (2611136069/5000000000 : ℝ), (-28994873/125000000 : ℝ)] ![(21784361084251/50000000000000 : ℝ), (42125174350349/100000000000000 : ℝ), (14306103459133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356185919/10000000000 : ℝ)|^515 ≤ (21784361084251/50000000000000 : ℝ)^387
        have hw : |(5356185919/10000000000 : ℝ)|=(5356185919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611136069/5000000000 : ℝ)|^515 ≤ (42125174350349/100000000000000 : ℝ)^387
        have hw : |(2611136069/5000000000 : ℝ)|=(2611136069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-28994873/125000000 : ℝ)|^515 ≤ (14306103459133/100000000000000 : ℝ)^387
        have hw : |(-28994873/125000000 : ℝ)|=(28994873/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s3_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4375274727/10000000000 : ℝ)*x 0 + (1042041199/2500000000 : ℝ)*x 1 + (574106877/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4375274727/10000000000 : ℝ)^515 ≤ (33286495366881/100000000000000 : ℝ)^387 := by
    have hnat : (4375274727 : ℕ)^515*100000000000000^387 ≤ 33286495366881^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4375274727 10000000000 33286495366881 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042041199/2500000000 : ℝ)^515 ≤ (3900784059941/12500000000000 : ℝ)^387 := by
    have hnat : (1042041199 : ℕ)^515*12500000000000^387 ≤ 3900784059941^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042041199 2500000000 3900784059941 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (574106877/1250000000 : ℝ)^515 ≤ (4438404016553/12500000000000 : ℝ)^387 := by
    have hnat : (574106877 : ℕ)^515*12500000000000^387 ≤ 4438404016553^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574106877 1250000000 4438404016553 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4375274727/10000000000 : ℝ), (1042041199/2500000000 : ℝ), (574106877/1250000000 : ℝ)] ![(33286495366881/100000000000000 : ℝ), (3900784059941/12500000000000 : ℝ), (4438404016553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4375274727/10000000000 : ℝ)|^515 ≤ (33286495366881/100000000000000 : ℝ)^387
        have hw : |(4375274727/10000000000 : ℝ)|=(4375274727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042041199/2500000000 : ℝ)|^515 ≤ (3900784059941/12500000000000 : ℝ)^387
        have hw : |(1042041199/2500000000 : ℝ)|=(1042041199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(574106877/1250000000 : ℝ)|^515 ≤ (4438404016553/12500000000000 : ℝ)^387
        have hw : |(574106877/1250000000 : ℝ)|=(574106877/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s3_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104087637/5000000000 : ℝ)*x 0 + (2611588153/5000000000 : ℝ)*x 1 + (2719438221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104087637/5000000000 : ℝ)^515 ≤ (6699510388031/50000000000000 : ℝ)^387 := by
    have hnat : (1104087637 : ℕ)^515*50000000000000^387 ≤ 6699510388031^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104087637 5000000000 6699510388031 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2611588153/5000000000 : ℝ)^515 ≤ (5266860043111/12500000000000 : ℝ)^387 := by
    have hnat : (2611588153 : ℕ)^515*12500000000000^387 ≤ 5266860043111^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611588153 5000000000 5266860043111 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719438221/5000000000 : ℝ)^515 ≤ (44466098859611/100000000000000 : ℝ)^387 := by
    have hnat : (2719438221 : ℕ)^515*100000000000000^387 ≤ 44466098859611^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719438221 5000000000 44466098859611 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104087637/5000000000 : ℝ), (2611588153/5000000000 : ℝ), (2719438221/5000000000 : ℝ)] ![(6699510388031/50000000000000 : ℝ), (5266860043111/12500000000000 : ℝ), (44466098859611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104087637/5000000000 : ℝ)|^515 ≤ (6699510388031/50000000000000 : ℝ)^387
        have hw : |(-1104087637/5000000000 : ℝ)|=(1104087637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2611588153/5000000000 : ℝ)|^515 ≤ (5266860043111/12500000000000 : ℝ)^387
        have hw : |(2611588153/5000000000 : ℝ)|=(2611588153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719438221/5000000000 : ℝ)|^515 ≤ (44466098859611/100000000000000 : ℝ)^387
        have hw : |(2719438221/5000000000 : ℝ)|=(2719438221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s3_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1325369059/2500000000 : ℝ)*x 0 + (-420597051/2000000000 : ℝ)*x 1 + (2719438361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325369059/2500000000 : ℝ)^515 ≤ (21488754747381/50000000000000 : ℝ)^387 := by
    have hnat : (1325369059 : ℕ)^515*50000000000000^387 ≤ 21488754747381^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325369059 2500000000 21488754747381 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (420597051/2000000000 : ℝ)^515 ≤ (6278194292043/50000000000000 : ℝ)^387 := by
    have hnat : (420597051 : ℕ)^515*50000000000000^387 ≤ 6278194292043^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420597051 2000000000 6278194292043 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719438361/5000000000 : ℝ)^515 ≤ (44466101905921/100000000000000 : ℝ)^387 := by
    have hnat : (2719438361 : ℕ)^515*100000000000000^387 ≤ 44466101905921^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719438361 5000000000 44466101905921 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325369059/2500000000 : ℝ), (-420597051/2000000000 : ℝ), (2719438361/5000000000 : ℝ)] ![(21488754747381/50000000000000 : ℝ), (6278194292043/50000000000000 : ℝ), (44466101905921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325369059/2500000000 : ℝ)|^515 ≤ (21488754747381/50000000000000 : ℝ)^387
        have hw : |(1325369059/2500000000 : ℝ)|=(1325369059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-420597051/2000000000 : ℝ)|^515 ≤ (6278194292043/50000000000000 : ℝ)^387
        have hw : |(-420597051/2000000000 : ℝ)|=(420597051/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719438361/5000000000 : ℝ)|^515 ≤ (44466101905921/100000000000000 : ℝ)^387
        have hw : |(2719438361/5000000000 : ℝ)|=(2719438361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s3_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5301475991/10000000000 : ℝ)*x 0 + (1359719169/2500000000 : ℝ)*x 1 + (-2102985651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301475991/10000000000 : ℝ)^515 ≤ (42977506851703/100000000000000 : ℝ)^387 := by
    have hnat : (5301475991 : ℕ)^515*100000000000000^387 ≤ 42977506851703^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301475991 10000000000 42977506851703 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359719169/2500000000 : ℝ)^515 ≤ (2779131337841/6250000000000 : ℝ)^387 := by
    have hnat : (1359719169 : ℕ)^515*6250000000000^387 ≤ 2779131337841^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359719169 2500000000 2779131337841 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2102985651/10000000000 : ℝ)^515 ≤ (1255639173053/10000000000000 : ℝ)^387 := by
    have hnat : (2102985651 : ℕ)^515*10000000000000^387 ≤ 1255639173053^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102985651 10000000000 1255639173053 10000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301475991/10000000000 : ℝ), (1359719169/2500000000 : ℝ), (-2102985651/10000000000 : ℝ)] ![(42977506851703/100000000000000 : ℝ), (2779131337841/6250000000000 : ℝ), (1255639173053/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301475991/10000000000 : ℝ)|^515 ≤ (42977506851703/100000000000000 : ℝ)^387
        have hw : |(5301475991/10000000000 : ℝ)|=(5301475991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359719169/2500000000 : ℝ)|^515 ≤ (2779131337841/6250000000000 : ℝ)^387
        have hw : |(1359719169/2500000000 : ℝ)|=(1359719169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2102985651/10000000000 : ℝ)|^515 ≤ (1255639173053/10000000000000 : ℝ)^387
        have hw : |(-2102985651/10000000000 : ℝ)|=(2102985651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s3_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2187660223/5000000000 : ℝ)*x 0 + (229554499/500000000 : ℝ)*x 1 + (833988139/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187660223/5000000000 : ℝ)^515 ≤ (33286958234161/100000000000000 : ℝ)^387 := by
    have hnat : (2187660223 : ℕ)^515*100000000000000^387 ≤ 33286958234161^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187660223 5000000000 33286958234161 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (229554499/500000000 : ℝ)^515 ≤ (35489074621637/100000000000000 : ℝ)^387 := by
    have hnat : (229554499 : ℕ)^515*100000000000000^387 ≤ 35489074621637^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229554499 500000000 35489074621637 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (833988139/2000000000 : ℝ)^515 ≤ (15611983568051/50000000000000 : ℝ)^387 := by
    have hnat : (833988139 : ℕ)^515*50000000000000^387 ≤ 15611983568051^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833988139 2000000000 15611983568051 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187660223/5000000000 : ℝ), (229554499/500000000 : ℝ), (833988139/2000000000 : ℝ)] ![(33286958234161/100000000000000 : ℝ), (35489074621637/100000000000000 : ℝ), (15611983568051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187660223/5000000000 : ℝ)|^515 ≤ (33286958234161/100000000000000 : ℝ)^387
        have hw : |(2187660223/5000000000 : ℝ)|=(2187660223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(229554499/500000000 : ℝ)|^515 ≤ (35489074621637/100000000000000 : ℝ)^387
        have hw : |(229554499/500000000 : ℝ)|=(229554499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(833988139/2000000000 : ℝ)|^515 ≤ (15611983568051/50000000000000 : ℝ)^387
        have hw : |(833988139/2000000000 : ℝ)|=(833988139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4201/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2583/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7467/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4201/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4309/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4201/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4309/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4201/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4309/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4201/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4309/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4201/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4309/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4201/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4309/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4309/50000 : ℝ) ^ (8239/2048 : ℝ) ≤ (521428025405493/10000000000000000000 : ℝ) := by
    have hpowers : (4309/50000 : ℝ)^8239 ≤ (521428025405493/10000000000000000000 : ℝ)^2048 := by
      have hnat : (4309 : ℕ)^8239*10000000000000000000^2048 ≤ 521428025405493^2048*50000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4309 50000 521428025405493 10000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4309/50000 : ℝ)) (X := (521428025405493/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4201/25000 : ℝ) ^ (8239/2048 : ℝ) ≤ (38268771589446453/50000000000000000000 : ℝ) := by
    have hpowers : (4201/25000 : ℝ)^8239 ≤ (38268771589446453/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4201 : ℕ)^8239*50000000000000000000^2048 ≤ 38268771589446453^2048*25000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4201 25000 38268771589446453 50000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4201/25000 : ℝ)) (X := (38268771589446453/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000521428025405493/5000000000000000000 : ℝ) ≤ (10000259216593591/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (5000521428025405493/5000000000000000000 : ℝ)^2048 ≤ (10000259216593591/10000000000000000 : ℝ)^8239 := by
      have hnat : (5000521428025405493 : ℕ)^2048*10000000000000000^8239 ≤ 10000259216593591^8239*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000521428025405493 5000000000000000000 10000259216593591 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000259216593591/10000000000000000 : ℝ)) (X := (5000521428025405493/5000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25020437955858236959/25000000000000000000 : ℝ) ≤ (250050787818033/250000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (25020437955858236959/25000000000000000000 : ℝ)^2048 ≤ (250050787818033/250000000000000 : ℝ)^8239 := by
      have hnat : (25020437955858236959 : ℕ)^2048*250000000000000^8239 ≤ 250050787818033^8239*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25020437955858236959 25000000000000000000 250050787818033 250000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250050787818033/250000000000000 : ℝ)) (X := (25020437955858236959/25000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25038268771589446453/25000000000000000000 : ℝ) ≤ (10003803808849049/10000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (25038268771589446453/25000000000000000000 : ℝ)^2048 ≤ (10003803808849049/10000000000000000 : ℝ)^8239 := by
      have hnat : (25038268771589446453 : ℕ)^2048*10000000000000000^8239 ≤ 10003803808849049^8239*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25038268771589446453 25000000000000000000 10003803808849049 10000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003803808849049/10000000000000000 : ℝ)) (X := (25038268771589446453/25000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(521428025405493/10000000000000000000 : ℝ) ≤ ((40915787325488799441/40930000000000000000 : ℝ)+2*(1772296127729/818600000000000 : ℝ)*(4309/50000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (40915787325488799441/40930000000000000000 : ℝ)+2*(1772296127729/818600000000000 : ℝ)*(4309/50000 : ℝ)=(10000259216593591/10000000000000000 : ℝ) by norm_num, show 1+2*(521428025405493/10000000000000000000 : ℝ)=(5000521428025405493/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38268771589446453/50000000000000000000 : ℝ)+(521428025405493/10000000000000000000 : ℝ) ≤ ((40915787325488799441/40930000000000000000 : ℝ)+(1772296127729/818600000000000 : ℝ)*((4201/25000 : ℝ)+(4309/50000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (40915787325488799441/40930000000000000000 : ℝ)+(1772296127729/818600000000000 : ℝ)*((4201/25000 : ℝ)+(4309/50000 : ℝ))=(250050787818033/250000000000000 : ℝ) by norm_num, show 1+(38268771589446453/50000000000000000000 : ℝ)+(521428025405493/10000000000000000000 : ℝ)=(25020437955858236959/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38268771589446453/50000000000000000000 : ℝ) ≤ ((40915787325488799441/40930000000000000000 : ℝ)+2*(1772296127729/818600000000000 : ℝ)*(4201/25000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (40915787325488799441/40930000000000000000 : ℝ)+2*(1772296127729/818600000000000 : ℝ)*(4201/25000 : ℝ)=(10003803808849049/10000000000000000 : ℝ) by norm_num, show 1+2*(38268771589446453/50000000000000000000 : ℝ)=(25038268771589446453/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40915787325488799441/40930000000000000000 : ℝ)*(X 1 0+X 2 0)+(1772296127729/818600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (4309/50000 : ℝ)) (hi := (4201/25000 : ℝ)) (c := (40915787325488799441/40930000000000000000 : ℝ)) (alpha := (1772296127729/818600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40915787325488799441/40930000000000000000 : ℝ)*(X 0 1+X 2 1)+(1772296127729/818600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (4309/50000 : ℝ)) (hi := (4201/25000 : ℝ)) (c := (40915787325488799441/40930000000000000000 : ℝ)) (alpha := (1772296127729/818600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40915787325488799441/40930000000000000000 : ℝ)*(X 0 2+X 1 2)+(1772296127729/818600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (4309/50000 : ℝ)) (hi := (4201/25000 : ℝ)) (c := (40915787325488799441/40930000000000000000 : ℝ)) (alpha := (1772296127729/818600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-441630289/2000000000 : ℝ)*X 0 0+(5439786659/10000000000 : ℝ)*X 0 1+(2611135849/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669523233/1250000000 : ℝ)*X 1 0+(-2319590219/10000000000 : ℝ)*X 1 1+(163195997/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356185919/10000000000 : ℝ)*X 2 0+(2611136069/5000000000 : ℝ)*X 2 1+(-28994873/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4375274727/10000000000 : ℝ)*X 0 0+(1042041199/2500000000 : ℝ)*X 0 1+(574106877/1250000000 : ℝ)*X 0 2+(4375274727/10000000000 : ℝ)*X 1 0+(1042041199/2500000000 : ℝ)*X 1 1+(574106877/1250000000 : ℝ)*X 1 2+(4375274727/10000000000 : ℝ)*X 2 0+(1042041199/2500000000 : ℝ)*X 2 1+(574106877/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1104087637/5000000000 : ℝ)*X 0 0+(2611588153/5000000000 : ℝ)*X 0 1+(2719438221/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325369059/2500000000 : ℝ)*X 1 0+(-420597051/2000000000 : ℝ)*X 1 1+(2719438361/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301475991/10000000000 : ℝ)*X 2 0+(1359719169/2500000000 : ℝ)*X 2 1+(-2102985651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187660223/5000000000 : ℝ)*X 0 0+(229554499/500000000 : ℝ)*X 0 1+(833988139/2000000000 : ℝ)*X 0 2+(2187660223/5000000000 : ℝ)*X 1 0+(229554499/500000000 : ℝ)*X 1 1+(833988139/2000000000 : ℝ)*X 1 2+(2187660223/5000000000 : ℝ)*X 2 0+(229554499/500000000 : ℝ)*X 2 1+(833988139/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11897511110766873065721954777/2046500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12540821/800000000000 : ℝ)*(base19) + (258082573/20000000000000 : ℝ)*(base23) + (173753959/100000000000000 : ℝ)*(lower2) + (27835181/50000000000000 : ℝ)*(upper3) + (10996839/6250000000000 : ℝ)*(upper5) + (3476066958249699/100000000000000 : ℝ)*(major0) + (3476066958249699/100000000000000 : ℝ)*(major1) + (3476066958249699/100000000000000 : ℝ)*(major2) + (459741431632597/10000000000000 : ℝ)*(sp0) + (4597449128122047/100000000000000 : ℝ)*(sp1) + (4597449405311807/100000000000000 : ℝ)*(sp2) + (1177335159192969/50000000000000 : ℝ)*(sp3) + (36379398701/100000000000000 : ℝ)*(sp4) + (12708602463/100000000000000 : ℝ)*(sp7) + (2354683026988401/100000000000000 : ℝ)*(f.failure) + (35917583560349/781250000000 : ℝ)*(f.sum) + (247272719777429/40930000000000000000000000000 : ℝ)*base66 + (18597219815143831741/4093000000000000000000000000000000 : ℝ)*base68 + (10974103791246831741/4093000000000000000000000000000000 : ℝ)*base70 + (5388776905587831741/4093000000000000000000000000000000 : ℝ)*base72 + (75579531014779/40930000000000000000000000000 : ℝ)*base74 + (26422128586255168259/4093000000000000000000000000000000 : ℝ)*base75 + (11322407293912831741/4093000000000000000000000000000000 : ℝ)*base78 + (23123054046266168259/4093000000000000000000000000000000 : ℝ)*base79 + (154273792715519/40930000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (5847819/5000000000000000000000 : ℝ)*base90 + (5847819/5000000000000000000000 : ℝ)*base92 + (5847819/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3519899499311479701358044189/511625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1720950547/100000000000000 : ℝ)*(base19) + (1474759443/100000000000000 : ℝ)*(base23) + (547109/6250000000000 : ℝ)*(upper2) + (65367811/25000000000000 : ℝ)*(upper3) + (30349813/50000000000000 : ℝ)*(upper5) + (876314328080619/25000000000000 : ℝ)*(major0) + (876314328080619/25000000000000 : ℝ)*(major1) + (876314328080619/25000000000000 : ℝ)*(major2) + (3770028883/12500000000000 : ℝ)*(sp1) + (12732379387/50000000000000 : ℝ)*(sp2) + (36219202048471/781250000000 : ℝ)*(sp4) + (4636025981022677/100000000000000 : ℝ)*(sp5) + (463603092268607/10000000000000 : ℝ)*(sp6) + (2374456533112563/100000000000000 : ℝ)*(sp7) + (2374456533112563/100000000000000 : ℝ)*(f.failure) + (36219202048471/781250000000 : ℝ)*(f.sum) + (12261616614497/5116250000000000000000000000 : ℝ)*base66 + (6166451584701683979/1023250000000000000000000000000000 : ℝ)*base67 + (8464450356374433979/1023250000000000000000000000000000 : ℝ)*base69 + (10671793402023183979/1023250000000000000000000000000000 : ℝ)*base71 + (106357469072883/20465000000000000000000000000 : ℝ)*base74 + (7267178936393933979/1023250000000000000000000000000000 : ℝ)*base75 + (6269193143637183979/1023250000000000000000000000000000 : ℝ)*base77 + (14627560529108683979/1023250000000000000000000000000000 : ℝ)*base79 + (62259189634573/20465000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (51495297/5000000000000000000000 : ℝ)*base90 + (51495297/5000000000000000000000 : ℝ)*base92 + (51495297/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1047_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4201/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1047_s4_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212020323/10000000000 : ℝ)*x 0 + (5406887887/10000000000 : ℝ)*x 1 + (2626321891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212020323/10000000000 : ℝ)^515 ≤ (6715039000769/50000000000000 : ℝ)^387 := by
    have hnat : (2212020323 : ℕ)^515*50000000000000^387 ≤ 6715039000769^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212020323 10000000000 6715039000769 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406887887/10000000000 : ℝ)^515 ≤ (11029603146247/25000000000000 : ℝ)^387 := by
    have hnat : (5406887887 : ℕ)^515*25000000000000^387 ≤ 11029603146247^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406887887 10000000000 11029603146247 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626321891/5000000000 : ℝ)^515 ≤ (5306438676141/12500000000000 : ℝ)^387 := by
    have hnat : (2626321891 : ℕ)^515*12500000000000^387 ≤ 5306438676141^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626321891 5000000000 5306438676141 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212020323/10000000000 : ℝ), (5406887887/10000000000 : ℝ), (2626321891/5000000000 : ℝ)] ![(6715039000769/50000000000000 : ℝ), (11029603146247/25000000000000 : ℝ), (5306438676141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212020323/10000000000 : ℝ)|^515 ≤ (6715039000769/50000000000000 : ℝ)^387
        have hw : |(-2212020323/10000000000 : ℝ)|=(2212020323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406887887/10000000000 : ℝ)|^515 ≤ (11029603146247/25000000000000 : ℝ)^387
        have hw : |(5406887887/10000000000 : ℝ)|=(5406887887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626321891/5000000000 : ℝ)|^515 ≤ (5306438676141/12500000000000 : ℝ)^387
        have hw : |(2626321891/5000000000 : ℝ)|=(2626321891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s4_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1337013439/2500000000 : ℝ)*x 0 + (-2290492051/10000000000 : ℝ)*x 1 + (262632151/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337013439/2500000000 : ℝ)^515 ≤ (21740358069969/50000000000000 : ℝ)^387 := by
    have hnat : (1337013439 : ℕ)^515*50000000000000^387 ≤ 21740358069969^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337013439 2500000000 21740358069969 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2290492051/10000000000 : ℝ)^515 ≤ (1758472829559/12500000000000 : ℝ)^387 := by
    have hnat : (2290492051 : ℕ)^515*12500000000000^387 ≤ 1758472829559^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2290492051 10000000000 1758472829559 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262632151/500000000 : ℝ)^515 ≤ (42451501213799/100000000000000 : ℝ)^387 := by
    have hnat : (262632151 : ℕ)^515*100000000000000^387 ≤ 42451501213799^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262632151 500000000 42451501213799 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337013439/2500000000 : ℝ), (-2290492051/10000000000 : ℝ), (262632151/500000000 : ℝ)] ![(21740358069969/50000000000000 : ℝ), (1758472829559/12500000000000 : ℝ), (42451501213799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337013439/2500000000 : ℝ)|^515 ≤ (21740358069969/50000000000000 : ℝ)^387
        have hw : |(1337013439/2500000000 : ℝ)|=(1337013439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2290492051/10000000000 : ℝ)|^515 ≤ (1758472829559/12500000000000 : ℝ)^387
        have hw : |(-2290492051/10000000000 : ℝ)|=(2290492051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(262632151/500000000 : ℝ)|^515 ≤ (42451501213799/100000000000000 : ℝ)^387
        have hw : |(262632151/500000000 : ℝ)|=(262632151/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s4_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5348054727/10000000000 : ℝ)*x 0 + (5252642321/10000000000 : ℝ)*x 1 + (-458098337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348054727/10000000000 : ℝ)^515 ≤ (43480726645431/100000000000000 : ℝ)^387 := by
    have hnat : (5348054727 : ℕ)^515*100000000000000^387 ≤ 43480726645431^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348054727 10000000000 43480726645431 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252642321/10000000000 : ℝ)^515 ≤ (42451493696037/100000000000000 : ℝ)^387 := by
    have hnat : (5252642321 : ℕ)^515*100000000000000^387 ≤ 42451493696037^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252642321 10000000000 42451493696037 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458098337/2000000000 : ℝ)^515 ≤ (7033889822537/50000000000000 : ℝ)^387 := by
    have hnat : (458098337 : ℕ)^515*50000000000000^387 ≤ 7033889822537^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458098337 2000000000 7033889822537 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348054727/10000000000 : ℝ), (5252642321/10000000000 : ℝ), (-458098337/2000000000 : ℝ)] ![(43480726645431/100000000000000 : ℝ), (42451493696037/100000000000000 : ℝ), (7033889822537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348054727/10000000000 : ℝ)|^515 ≤ (43480726645431/100000000000000 : ℝ)^387
        have hw : |(5348054727/10000000000 : ℝ)|=(5348054727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252642321/10000000000 : ℝ)|^515 ≤ (42451493696037/100000000000000 : ℝ)^387
        have hw : |(5252642321/10000000000 : ℝ)|=(5252642321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-458098337/2000000000 : ℝ)|^515 ≤ (7033889822537/50000000000000 : ℝ)^387
        have hw : |(-458098337/2000000000 : ℝ)|=(458098337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s4_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (875514307/2000000000 : ℝ)*x 0 + (84592571/200000000 : ℝ)*x 1 + (4530788161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875514307/2000000000 : ℝ)^515 ≤ (33309750637461/100000000000000 : ℝ)^387 := by
    have hnat : (875514307 : ℕ)^515*100000000000000^387 ≤ 33309750637461^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875514307 2000000000 33309750637461 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84592571/200000000 : ℝ)^515 ≤ (15910064373581/50000000000000 : ℝ)^387 := by
    have hnat : (84592571 : ℕ)^515*50000000000000^387 ≤ 15910064373581^387*200000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84592571 200000000 15910064373581 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530788161/10000000000 : ℝ)^515 ≤ (34870120588937/100000000000000 : ℝ)^387 := by
    have hnat : (4530788161 : ℕ)^515*100000000000000^387 ≤ 34870120588937^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530788161 10000000000 34870120588937 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875514307/2000000000 : ℝ), (84592571/200000000 : ℝ), (4530788161/10000000000 : ℝ)] ![(33309750637461/100000000000000 : ℝ), (15910064373581/50000000000000 : ℝ), (34870120588937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875514307/2000000000 : ℝ)|^515 ≤ (33309750637461/100000000000000 : ℝ)^387
        have hw : |(875514307/2000000000 : ℝ)|=(875514307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84592571/200000000 : ℝ)|^515 ≤ (15910064373581/50000000000000 : ℝ)^387
        have hw : |(84592571/200000000 : ℝ)|=(84592571/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530788161/10000000000 : ℝ)|^515 ≤ (34870120588937/100000000000000 : ℝ)^387
        have hw : |(4530788161/10000000000 : ℝ)|=(4530788161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s4_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-110601431/500000000 : ℝ)*x 0 + (5253098729/10000000000 : ℝ)*x 1 + (2703215543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110601431/500000000 : ℝ)^515 ≤ (209846016209/1562500000000 : ℝ)^387 := by
    have hnat : (110601431 : ℕ)^515*1562500000000^387 ≤ 209846016209^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110601431 500000000 209846016209 1562500000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253098729/10000000000 : ℝ)^515 ≤ (10614100611469/25000000000000 : ℝ)^387 := by
    have hnat : (5253098729 : ℕ)^515*25000000000000^387 ≤ 10614100611469^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253098729 10000000000 10614100611469 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703215543/5000000000 : ℝ)^515 ≤ (551418156159/1250000000000 : ℝ)^387 := by
    have hnat : (2703215543 : ℕ)^515*1250000000000^387 ≤ 551418156159^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703215543 5000000000 551418156159 1250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-110601431/500000000 : ℝ), (5253098729/10000000000 : ℝ), (2703215543/5000000000 : ℝ)] ![(209846016209/1562500000000 : ℝ), (10614100611469/25000000000000 : ℝ), (551418156159/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-110601431/500000000 : ℝ)|^515 ≤ (209846016209/1562500000000 : ℝ)^387
        have hw : |(-110601431/500000000 : ℝ)|=(110601431/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253098729/10000000000 : ℝ)|^515 ≤ (10614100611469/25000000000000 : ℝ)^387
        have hw : |(5253098729/10000000000 : ℝ)|=(5253098729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703215543/5000000000 : ℝ)|^515 ≤ (551418156159/1250000000000 : ℝ)^387
        have hw : |(2703215543/5000000000 : ℝ)|=(2703215543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s4_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5309263111/10000000000 : ℝ)*x 0 + (-1068352139/5000000000 : ℝ)*x 1 + (5406431057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309263111/10000000000 : ℝ)^515 ≤ (1345672957899/3125000000000 : ℝ)^387 := by
    have hnat : (5309263111 : ℕ)^515*3125000000000^387 ≤ 1345672957899^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309263111 10000000000 1345672957899 3125000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1068352139/5000000000 : ℝ)^515 ≤ (3206253288927/25000000000000 : ℝ)^387 := by
    have hnat : (1068352139 : ℕ)^515*25000000000000^387 ≤ 3206253288927^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068352139 5000000000 3206253288927 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406431057/10000000000 : ℝ)^515 ≤ (44113452177833/100000000000000 : ℝ)^387 := by
    have hnat : (5406431057 : ℕ)^515*100000000000000^387 ≤ 44113452177833^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406431057 10000000000 44113452177833 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309263111/10000000000 : ℝ), (-1068352139/5000000000 : ℝ), (5406431057/10000000000 : ℝ)] ![(1345672957899/3125000000000 : ℝ), (3206253288927/25000000000000 : ℝ), (44113452177833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309263111/10000000000 : ℝ)|^515 ≤ (1345672957899/3125000000000 : ℝ)^387
        have hw : |(5309263111/10000000000 : ℝ)|=(5309263111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1068352139/5000000000 : ℝ)|^515 ≤ (3206253288927/25000000000000 : ℝ)^387
        have hw : |(-1068352139/5000000000 : ℝ)|=(1068352139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406431057/10000000000 : ℝ)|^515 ≤ (44113452177833/100000000000000 : ℝ)^387
        have hw : |(5406431057/10000000000 : ℝ)|=(5406431057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s4_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5309263109/10000000000 : ℝ)*x 0 + (2703215527/5000000000 : ℝ)*x 1 + (-534176071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309263109/10000000000 : ℝ)^515 ≤ (21530767315591/50000000000000 : ℝ)^387 := by
    have hnat : (5309263109 : ℕ)^515*50000000000000^387 ≤ 21530767315591^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309263109 10000000000 21530767315591 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703215527/5000000000 : ℝ)^515 ≤ (22056726072629/50000000000000 : ℝ)^387 := by
    have hnat : (2703215527 : ℕ)^515*50000000000000^387 ≤ 22056726072629^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703215527 5000000000 22056726072629 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (534176071/2500000000 : ℝ)^515 ≤ (12825013203633/100000000000000 : ℝ)^387 := by
    have hnat : (534176071 : ℕ)^515*100000000000000^387 ≤ 12825013203633^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534176071 2500000000 12825013203633 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309263109/10000000000 : ℝ), (2703215527/5000000000 : ℝ), (-534176071/2500000000 : ℝ)] ![(21530767315591/50000000000000 : ℝ), (22056726072629/50000000000000 : ℝ), (12825013203633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309263109/10000000000 : ℝ)|^515 ≤ (21530767315591/50000000000000 : ℝ)^387
        have hw : |(5309263109/10000000000 : ℝ)|=(5309263109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703215527/5000000000 : ℝ)|^515 ≤ (22056726072629/50000000000000 : ℝ)^387
        have hw : |(2703215527/5000000000 : ℝ)|=(2703215527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-534176071/2500000000 : ℝ)|^515 ≤ (12825013203633/100000000000000 : ℝ)^387
        have hw : |(-534176071/2500000000 : ℝ)|=(534176071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s4_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (875517933/2000000000 : ℝ)*x 0 + (2264948741/5000000000 : ℝ)*x 1 + (4230521327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875517933/2000000000 : ℝ)^515 ≤ (1332397368819/4000000000000 : ℝ)^387 := by
    have hnat : (875517933 : ℕ)^515*4000000000000^387 ≤ 1332397368819^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875517933 2000000000 1332397368819 4000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264948741/5000000000 : ℝ)^515 ≤ (6972199747271/20000000000000 : ℝ)^387 := by
    have hnat : (2264948741 : ℕ)^515*20000000000000^387 ≤ 6972199747271^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264948741 5000000000 6972199747271 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230521327/10000000000 : ℝ)^515 ≤ (31829067030549/100000000000000 : ℝ)^387 := by
    have hnat : (4230521327 : ℕ)^515*100000000000000^387 ≤ 31829067030549^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230521327 10000000000 31829067030549 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875517933/2000000000 : ℝ), (2264948741/5000000000 : ℝ), (4230521327/10000000000 : ℝ)] ![(1332397368819/4000000000000 : ℝ), (6972199747271/20000000000000 : ℝ), (31829067030549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875517933/2000000000 : ℝ)|^515 ≤ (1332397368819/4000000000000 : ℝ)^387
        have hw : |(875517933/2000000000 : ℝ)|=(875517933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264948741/5000000000 : ℝ)|^515 ≤ (6972199747271/20000000000000 : ℝ)^387
        have hw : |(2264948741/5000000000 : ℝ)|=(2264948741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230521327/10000000000 : ℝ)|^515 ≤ (31829067030549/100000000000000 : ℝ)^387
        have hw : |(4230521327/10000000000 : ℝ)|=(4230521327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10981/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14247/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7467/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2583/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7467/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2583/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7467/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2583/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7467/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2583/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7467/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2583/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7467/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2583/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2583/25000 : ℝ) ^ (8239/2048 : ℝ) ≤ (2704293976196729/25000000000000000000 : ℝ) := by
    have hpowers : (2583/25000 : ℝ)^8239 ≤ (2704293976196729/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2583 : ℕ)^8239*25000000000000000000^2048 ≤ 2704293976196729^2048*25000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2583 25000 2704293976196729 25000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2583/25000 : ℝ)) (X := (2704293976196729/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7467/50000 : ℝ) ^ (8239/2048 : ℝ) ≤ (9523192680170383/20000000000000000000 : ℝ) := by
    have hpowers : (7467/50000 : ℝ)^8239 ≤ (9523192680170383/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7467 : ℕ)^8239*20000000000000000000^2048 ≤ 9523192680170383^2048*50000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7467 50000 9523192680170383 20000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7467/50000 : ℝ)) (X := (9523192680170383/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502704293976196729/12500000000000000000 : ℝ) ≤ (5000268864859441/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (12502704293976196729/12500000000000000000 : ℝ)^2048 ≤ (5000268864859441/5000000000000000 : ℝ)^8239 := by
      have hnat : (12502704293976196729 : ℕ)^2048*5000000000000000^8239 ≤ 5000268864859441^8239*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502704293976196729 12500000000000000000 5000268864859441 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268864859441/5000000000000000 : ℝ)) (X := (12502704293976196729/12500000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058433139305638831/100000000000000000000 : ℝ) ≤ (2000290435260487/2000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (100058433139305638831/100000000000000000000 : ℝ)^2048 ≤ (2000290435260487/2000000000000000 : ℝ)^8239 := by
      have hnat : (100058433139305638831 : ℕ)^2048*2000000000000000^8239 ≤ 2000290435260487^8239*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058433139305638831 100000000000000000000 2000290435260487 2000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000290435260487/2000000000000000 : ℝ)) (X := (100058433139305638831/100000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10009523192680170383/10000000000000000000 : ℝ) ≤ (2500591655721497/2500000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (10009523192680170383/10000000000000000000 : ℝ)^2048 ≤ (2500591655721497/2500000000000000 : ℝ)^8239 := by
      have hnat : (10009523192680170383 : ℕ)^2048*2500000000000000^8239 ≤ 2500591655721497^8239*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10009523192680170383 10000000000000000000 2500591655721497 2500000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500591655721497/2500000000000000 : ℝ)) (X := (10009523192680170383/10000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2704293976196729/25000000000000000000 : ℝ) ≤ ((3833631542330312981/3835000000000000000 : ℝ)+2*(304815527851/153400000000000 : ℝ)*(2583/25000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (3833631542330312981/3835000000000000000 : ℝ)+2*(304815527851/153400000000000 : ℝ)*(2583/25000 : ℝ)=(5000268864859441/5000000000000000 : ℝ) by norm_num, show 1+2*(2704293976196729/25000000000000000000 : ℝ)=(12502704293976196729/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9523192680170383/20000000000000000000 : ℝ)+(2704293976196729/25000000000000000000 : ℝ) ≤ ((3833631542330312981/3835000000000000000 : ℝ)+(304815527851/153400000000000 : ℝ)*((7467/50000 : ℝ)+(2583/25000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (3833631542330312981/3835000000000000000 : ℝ)+(304815527851/153400000000000 : ℝ)*((7467/50000 : ℝ)+(2583/25000 : ℝ))=(2000290435260487/2000000000000000 : ℝ) by norm_num, show 1+(9523192680170383/20000000000000000000 : ℝ)+(2704293976196729/25000000000000000000 : ℝ)=(100058433139305638831/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9523192680170383/20000000000000000000 : ℝ) ≤ ((3833631542330312981/3835000000000000000 : ℝ)+2*(304815527851/153400000000000 : ℝ)*(7467/50000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (3833631542330312981/3835000000000000000 : ℝ)+2*(304815527851/153400000000000 : ℝ)*(7467/50000 : ℝ)=(2500591655721497/2500000000000000 : ℝ) by norm_num, show 1+2*(9523192680170383/20000000000000000000 : ℝ)=(10009523192680170383/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3833631542330312981/3835000000000000000 : ℝ)*(X 1 0+X 2 0)+(304815527851/153400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (2583/25000 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (3833631542330312981/3835000000000000000 : ℝ)) (alpha := (304815527851/153400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3833631542330312981/3835000000000000000 : ℝ)*(X 0 1+X 2 1)+(304815527851/153400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (2583/25000 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (3833631542330312981/3835000000000000000 : ℝ)) (alpha := (304815527851/153400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3833631542330312981/3835000000000000000 : ℝ)*(X 0 2+X 1 2)+(304815527851/153400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (2583/25000 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (3833631542330312981/3835000000000000000 : ℝ)) (alpha := (304815527851/153400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2212020323/10000000000 : ℝ)*X 0 0+(5406887887/10000000000 : ℝ)*X 0 1+(2626321891/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337013439/2500000000 : ℝ)*X 1 0+(-2290492051/10000000000 : ℝ)*X 1 1+(262632151/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348054727/10000000000 : ℝ)*X 2 0+(5252642321/10000000000 : ℝ)*X 2 1+(-458098337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875514307/2000000000 : ℝ)*X 0 0+(84592571/200000000 : ℝ)*X 0 1+(4530788161/10000000000 : ℝ)*X 0 2+(875514307/2000000000 : ℝ)*X 1 0+(84592571/200000000 : ℝ)*X 1 1+(4530788161/10000000000 : ℝ)*X 1 2+(875514307/2000000000 : ℝ)*X 2 0+(84592571/200000000 : ℝ)*X 2 1+(4530788161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-110601431/500000000 : ℝ)*X 0 0+(5253098729/10000000000 : ℝ)*X 0 1+(2703215543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309263111/10000000000 : ℝ)*X 1 0+(-1068352139/5000000000 : ℝ)*X 1 1+(5406431057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5309263109/10000000000 : ℝ)*X 2 0+(2703215527/5000000000 : ℝ)*X 2 1+(-534176071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875517933/2000000000 : ℝ)*X 0 0+(2264948741/5000000000 : ℝ)*X 0 1+(4230521327/10000000000 : ℝ)*X 0 2+(875517933/2000000000 : ℝ)*X 1 0+(2264948741/5000000000 : ℝ)*X 1 1+(4230521327/10000000000 : ℝ)*X 1 2+(875517933/2000000000 : ℝ)*X 2 0+(2264948741/5000000000 : ℝ)*X 2 1+(4230521327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33884018183943095095422243/95875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191687003/12500000000000 : ℝ)*(base19) + (735699321/50000000000000 : ℝ)*(base23) + (82732571/100000000000000 : ℝ)*(lower3) + (82841697/12500000000000 : ℝ)*(upper4) + (32732891/12500000000000 : ℝ)*(lower5) + (2450946874276899/50000000000000 : ℝ)*(major0) + (2450946874276899/50000000000000 : ℝ)*(major1) + (2450946874276899/50000000000000 : ℝ)*(major2) + (648323073667807/10000000000000 : ℝ)*(sp0) + (6483249797477887/100000000000000 : ℝ)*(sp1) + (648324985957527/10000000000000 : ℝ)*(sp2) + (3320510513086163/100000000000000 : ℝ)*(sp3) + (20594295841/100000000000000 : ℝ)*(sp4) + (6410316723/25000000000000 : ℝ)*(sp7) + (664107230870611/20000000000000 : ℝ)*(f.failure) + (6483251330973911/100000000000000 : ℝ)*(f.sum) + (1695974015953/479375000000000000000000000 : ℝ)*base65 + (2571166134606600919/191750000000000000000000000000000 : ℝ)*base67 + (774017596421600919/191750000000000000000000000000000 : ℝ)*base69 + (18400075074600919/191750000000000000000000000000000 : ℝ)*base71 + (10074157319977/1917500000000000000000000000 : ℝ)*base73 + (1904868859817899081/191750000000000000000000000000000 : ℝ)*base76 + (778016220148100919/191750000000000000000000000000000 : ℝ)*base77 + (1259687749292649081/191750000000000000000000000000000 : ℝ)*base80 + (1909540841127/1917500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1531809/1000000000000000000000 : ℝ)*base90 + (1531809/1000000000000000000000 : ℝ)*base92 + (1531809/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (876606744204221928536777091/95875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (979923027/50000000000000 : ℝ)*(base19) + (198993709/10000000000000 : ℝ)*(base23) + (113321909/100000000000000 : ℝ)*(upper3) + (42881471/100000000000000 : ℝ)*(lower4) + (45461147/12500000000000 : ℝ)*(upper5) + (4931032198400937/100000000000000 : ℝ)*(major0) + (4931032198400937/100000000000000 : ℝ)*(major1) + (4931032198400937/100000000000000 : ℝ)*(major2) + (24970527937/50000000000000 : ℝ)*(sp1) + (43340183913/100000000000000 : ℝ)*(sp2) + (1630447397850569/25000000000000 : ℝ)*(sp4) + (1630434422625087/25000000000000 : ℝ)*(sp5) + (6521744261281273/100000000000000 : ℝ)*(sp6) + (1670137250312703/50000000000000 : ℝ)*(sp7) + (1670137250312703/50000000000000 : ℝ)*(f.failure) + (1630447397850569/25000000000000 : ℝ)*(f.sum) + (10849357306513/7670000000000000000000000000 : ℝ)*base66 + (2985242581772661803/383500000000000000000000000000000 : ℝ)*base68 + (1589893012360338197/383500000000000000000000000000000 : ℝ)*base69 + (3412967596983661803/383500000000000000000000000000000 : ℝ)*base72 + (8485398142193/7670000000000000000000000000 : ℝ)*base74 + (9913210802569661803/383500000000000000000000000000000 : ℝ)*base76 + (2055315905639661803/383500000000000000000000000000000 : ℝ)*base78 + (3038827737091161803/383500000000000000000000000000000 : ℝ)*base80 + (53741193348637/7670000000000000000000000000 : ℝ)*base81 + (9645957/2500000000000000000000 : ℝ)*base90 + (9645957/2500000000000000000000 : ℝ)*base92 + (9645957/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1047_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2583/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10981/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1047_s5_0 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2212903827/10000000000 : ℝ)*x 0 + (5397553207/10000000000 : ℝ)*x 1 + (2630699691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2212903827/10000000000 : ℝ)^515 ≤ (6718608381653/50000000000000 : ℝ)^387 := by
    have hnat : (2212903827 : ℕ)^515*50000000000000^387 ≤ 6718608381653^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212903827 10000000000 6718608381653 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397553207/10000000000 : ℝ)^515 ≤ (8803416231951/20000000000000 : ℝ)^387 := by
    have hnat : (5397553207 : ℕ)^515*20000000000000^387 ≤ 8803416231951^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397553207 10000000000 8803416231951 20000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630699691/5000000000 : ℝ)^515 ≤ (10636425515111/25000000000000 : ℝ)^387 := by
    have hnat : (2630699691 : ℕ)^515*25000000000000^387 ≤ 10636425515111^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630699691 5000000000 10636425515111 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2212903827/10000000000 : ℝ), (5397553207/10000000000 : ℝ), (2630699691/5000000000 : ℝ)] ![(6718608381653/50000000000000 : ℝ), (8803416231951/20000000000000 : ℝ), (10636425515111/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2212903827/10000000000 : ℝ)|^515 ≤ (6718608381653/50000000000000 : ℝ)^387
        have hw : |(-2212903827/10000000000 : ℝ)|=(2212903827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397553207/10000000000 : ℝ)|^515 ≤ (8803416231951/20000000000000 : ℝ)^387
        have hw : |(5397553207/10000000000 : ℝ)|=(5397553207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630699691/5000000000 : ℝ)|^515 ≤ (10636425515111/25000000000000 : ℝ)^387
        have hw : |(2630699691/5000000000 : ℝ)|=(2630699691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s5_1 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345733559/10000000000 : ℝ)*x 0 + (-2282032293/10000000000 : ℝ)*x 1 + (1052279901/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345733559/10000000000 : ℝ)^515 ≤ (347644921183/800000000000 : ℝ)^387 := by
    have hnat : (5345733559 : ℕ)^515*800000000000^387 ≤ 347644921183^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345733559 10000000000 347644921183 800000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2282032293/10000000000 : ℝ)^515 ≤ (6999340725533/50000000000000 : ℝ)^387 := by
    have hnat : (2282032293 : ℕ)^515*50000000000000^387 ≤ 6999340725533^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282032293 10000000000 6999340725533 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052279901/2000000000 : ℝ)^515 ≤ (42545703384041/100000000000000 : ℝ)^387 := by
    have hnat : (1052279901 : ℕ)^515*100000000000000^387 ≤ 42545703384041^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052279901 2000000000 42545703384041 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345733559/10000000000 : ℝ), (-2282032293/10000000000 : ℝ), (1052279901/2000000000 : ℝ)] ![(347644921183/800000000000 : ℝ), (6999340725533/50000000000000 : ℝ), (42545703384041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345733559/10000000000 : ℝ)|^515 ≤ (347644921183/800000000000 : ℝ)^387
        have hw : |(5345733559/10000000000 : ℝ)|=(5345733559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2282032293/10000000000 : ℝ)|^515 ≤ (6999340725533/50000000000000 : ℝ)^387
        have hw : |(-2282032293/10000000000 : ℝ)|=(2282032293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052279901/2000000000 : ℝ)|^515 ≤ (42545703384041/100000000000000 : ℝ)^387
        have hw : |(1052279901/2000000000 : ℝ)|=(1052279901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s5_2 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5345733499/10000000000 : ℝ)*x 0 + (657674947/1250000000 : ℝ)*x 1 + (-2282032279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345733499/10000000000 : ℝ)^515 ≤ (43455614498813/100000000000000 : ℝ)^387 := by
    have hnat : (5345733499 : ℕ)^515*100000000000000^387 ≤ 43455614498813^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345733499 10000000000 43455614498813 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657674947/1250000000 : ℝ)^515 ≤ (42545704148069/100000000000000 : ℝ)^387 := by
    have hnat : (657674947 : ℕ)^515*100000000000000^387 ≤ 42545704148069^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657674947 1250000000 42545704148069 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282032279/10000000000 : ℝ)^515 ≤ (13998681336781/100000000000000 : ℝ)^387 := by
    have hnat : (2282032279 : ℕ)^515*100000000000000^387 ≤ 13998681336781^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282032279 10000000000 13998681336781 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345733499/10000000000 : ℝ), (657674947/1250000000 : ℝ), (-2282032279/10000000000 : ℝ)] ![(43455614498813/100000000000000 : ℝ), (42545704148069/100000000000000 : ℝ), (13998681336781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345733499/10000000000 : ℝ)|^515 ≤ (43455614498813/100000000000000 : ℝ)^387
        have hw : |(5345733499/10000000000 : ℝ)|=(5345733499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657674947/1250000000 : ℝ)|^515 ≤ (42545704148069/100000000000000 : ℝ)^387
        have hw : |(657674947/1250000000 : ℝ)|=(657674947/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282032279/10000000000 : ℝ)|^515 ≤ (13998681336781/100000000000000 : ℝ)^387
        have hw : |(-2282032279/10000000000 : ℝ)|=(2282032279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s5_3 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (875617357/2000000000 : ℝ)*x 0 + (530902707/1250000000 : ℝ)*x 1 + (4513058039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875617357/2000000000 : ℝ)^515 ≤ (8328742029529/25000000000000 : ℝ)^387 := by
    have hnat : (875617357 : ℕ)^515*25000000000000^387 ≤ 8328742029529^387*2000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875617357 2000000000 8328742029529 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530902707/1250000000 : ℝ)^515 ≤ (31996381881121/100000000000000 : ℝ)^387 := by
    have hnat : (530902707 : ℕ)^515*100000000000000^387 ≤ 31996381881121^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530902707 1250000000 31996381881121 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513058039/10000000000 : ℝ)^515 ≤ (17344324991709/50000000000000 : ℝ)^387 := by
    have hnat : (4513058039 : ℕ)^515*50000000000000^387 ≤ 17344324991709^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513058039 10000000000 17344324991709 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875617357/2000000000 : ℝ), (530902707/1250000000 : ℝ), (4513058039/10000000000 : ℝ)] ![(8328742029529/25000000000000 : ℝ), (31996381881121/100000000000000 : ℝ), (17344324991709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875617357/2000000000 : ℝ)|^515 ≤ (8328742029529/25000000000000 : ℝ)^387
        have hw : |(875617357/2000000000 : ℝ)|=(875617357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530902707/1250000000 : ℝ)|^515 ≤ (31996381881121/100000000000000 : ℝ)^387
        have hw : |(530902707/1250000000 : ℝ)|=(530902707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513058039/10000000000 : ℝ)|^515 ≤ (17344324991709/50000000000000 : ℝ)^387
        have hw : |(4513058039/10000000000 : ℝ)|=(4513058039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s5_4 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-553227391/2500000000 : ℝ)*x 0 + (5261754679/10000000000 : ℝ)*x 1 + (269859831/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553227391/2500000000 : ℝ)^515 ≤ (3359315780417/25000000000000 : ℝ)^387 := by
    have hnat : (553227391 : ℕ)^515*25000000000000^387 ≤ 3359315780417^387*2500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553227391 2500000000 3359315780417 25000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261754679/10000000000 : ℝ)^515 ≤ (42549525437059/100000000000000 : ℝ)^387 := by
    have hnat : (5261754679 : ℕ)^515*100000000000000^387 ≤ 42549525437059^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261754679 10000000000 42549525437059 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269859831/500000000 : ℝ)^515 ≤ (2750825713987/6250000000000 : ℝ)^387 := by
    have hnat : (269859831 : ℕ)^515*6250000000000^387 ≤ 2750825713987^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269859831 500000000 2750825713987 6250000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553227391/2500000000 : ℝ), (5261754679/10000000000 : ℝ), (269859831/500000000 : ℝ)] ![(3359315780417/25000000000000 : ℝ), (42549525437059/100000000000000 : ℝ), (2750825713987/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553227391/2500000000 : ℝ)|^515 ≤ (3359315780417/25000000000000 : ℝ)^387
        have hw : |(-553227391/2500000000 : ℝ)|=(553227391/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261754679/10000000000 : ℝ)|^515 ≤ (42549525437059/100000000000000 : ℝ)^387
        have hw : |(5261754679/10000000000 : ℝ)|=(5261754679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269859831/500000000 : ℝ)|^515 ≤ (2750825713987/6250000000000 : ℝ)^387
        have hw : |(269859831/500000000 : ℝ)|=(269859831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s5_5 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5311491937/10000000000 : ℝ)*x 0 + (-2146235041/10000000000 : ℝ)*x 1 + (5397196619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311491937/10000000000 : ℝ)^515 ≤ (43085592559187/100000000000000 : ℝ)^387 := by
    have hnat : (5311491937 : ℕ)^515*100000000000000^387 ≤ 43085592559187^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311491937 10000000000 43085592559187 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146235041/10000000000 : ℝ)^515 ≤ (12901196012903/100000000000000 : ℝ)^387 := by
    have hnat : (2146235041 : ℕ)^515*100000000000000^387 ≤ 12901196012903^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146235041 10000000000 12901196012903 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5397196619/10000000000 : ℝ)^515 ≤ (2200660570647/5000000000000 : ℝ)^387 := by
    have hnat : (5397196619 : ℕ)^515*5000000000000^387 ≤ 2200660570647^387*10000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397196619 10000000000 2200660570647 5000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311491937/10000000000 : ℝ), (-2146235041/10000000000 : ℝ), (5397196619/10000000000 : ℝ)] ![(43085592559187/100000000000000 : ℝ), (12901196012903/100000000000000 : ℝ), (2200660570647/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311491937/10000000000 : ℝ)|^515 ≤ (43085592559187/100000000000000 : ℝ)^387
        have hw : |(5311491937/10000000000 : ℝ)|=(5311491937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146235041/10000000000 : ℝ)|^515 ≤ (12901196012903/100000000000000 : ℝ)^387
        have hw : |(-2146235041/10000000000 : ℝ)|=(2146235041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5397196619/10000000000 : ℝ)|^515 ≤ (2200660570647/5000000000000 : ℝ)^387
        have hw : |(5397196619/10000000000 : ℝ)|=(5397196619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s5_6 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (265574597/500000000 : ℝ)*x 0 + (2698598311/5000000000 : ℝ)*x 1 + (-1073117517/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265574597/500000000 : ℝ)^515 ≤ (43085592591571/100000000000000 : ℝ)^387 := by
    have hnat : (265574597 : ℕ)^515*100000000000000^387 ≤ 43085592591571^387*500000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265574597 500000000 43085592591571 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698598311/5000000000 : ℝ)^515 ≤ (5501651430687/12500000000000 : ℝ)^387 := by
    have hnat : (2698598311 : ℕ)^515*12500000000000^387 ≤ 5501651430687^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698598311 5000000000 5501651430687 12500000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073117517/5000000000 : ℝ)^515 ≤ (12901195956909/100000000000000 : ℝ)^387 := by
    have hnat : (1073117517 : ℕ)^515*100000000000000^387 ≤ 12901195956909^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073117517 5000000000 12901195956909 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265574597/500000000 : ℝ), (2698598311/5000000000 : ℝ), (-1073117517/5000000000 : ℝ)] ![(43085592591571/100000000000000 : ℝ), (5501651430687/12500000000000 : ℝ), (12901195956909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265574597/500000000 : ℝ)|^515 ≤ (43085592591571/100000000000000 : ℝ)^387
        have hw : |(265574597/500000000 : ℝ)|=(265574597/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698598311/5000000000 : ℝ)|^515 ≤ (5501651430687/12500000000000 : ℝ)^387
        have hw : |(2698598311/5000000000 : ℝ)|=(2698598311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073117517/5000000000 : ℝ)|^515 ≤ (12901195956909/100000000000000 : ℝ)^387
        have hw : |(-1073117517/5000000000 : ℝ)|=(1073117517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1047_s5_7 (p : ℝ) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ)) (x : Fin 3 → ℝ) :
    (273631127/625000000 : ℝ)*x 0 + (2256182219/5000000000 : ℝ)*x 1 + (530989741/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273631127/625000000 : ℝ)^515 ≤ (16657541004397/50000000000000 : ℝ)^387 := by
    have hnat : (273631127 : ℕ)^515*50000000000000^387 ≤ 16657541004397^387*625000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273631127 625000000 16657541004397 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2256182219/5000000000 : ℝ)^515 ≤ (17340777826469/50000000000000 : ℝ)^387 := by
    have hnat : (2256182219 : ℕ)^515*50000000000000^387 ≤ 17340777826469^387*5000000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256182219 5000000000 17340777826469 50000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (530989741/1250000000 : ℝ)^515 ≤ (32003362322961/100000000000000 : ℝ)^387 := by
    have hnat : (530989741 : ℕ)^515*100000000000000^387 ≤ 32003362322961^387*1250000000^515 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530989741 1250000000 32003362322961 100000000000000 515 387 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (515/128 : ℝ)) 515 387 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273631127/625000000 : ℝ), (2256182219/5000000000 : ℝ), (530989741/1250000000 : ℝ)] ![(16657541004397/50000000000000 : ℝ), (17340777826469/50000000000000 : ℝ), (32003362322961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273631127/625000000 : ℝ)|^515 ≤ (16657541004397/50000000000000 : ℝ)^387
        have hw : |(273631127/625000000 : ℝ)|=(273631127/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2256182219/5000000000 : ℝ)|^515 ≤ (17340777826469/50000000000000 : ℝ)^387
        have hw : |(2256182219/5000000000 : ℝ)|=(2256182219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(530989741/1250000000 : ℝ)|^515 ≤ (32003362322961/100000000000000 : ℝ)^387
        have hw : |(530989741/1250000000 : ℝ)|=(530989741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1047_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10981/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11167/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10981/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10981/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10981/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10981/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10981/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10981/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10981/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (13821368530832573/100000000000000000000 : ℝ) := by
    have hpowers : (10981/100000 : ℝ)^8239 ≤ (13821368530832573/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10981 : ℕ)^8239*100000000000000000000^2048 ≤ 13821368530832573^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10981 100000 13821368530832573 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10981/100000 : ℝ)) (X := (13821368530832573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14247/100000 : ℝ) ^ (8239/2048 : ℝ) ≤ (39397830820604223/100000000000000000000 : ℝ) := by
    have hpowers : (14247/100000 : ℝ)^8239 ≤ (39397830820604223/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14247 : ℕ)^8239*100000000000000000000^2048 ≤ 39397830820604223^2048*100000^8239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14247 100000 39397830820604223 100000000000000000000 8239 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14247/100000 : ℝ)) (X := (39397830820604223/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013821368530832573/50000000000000000000 : ℝ) ≤ (5000343527411357/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50013821368530832573/50000000000000000000 : ℝ)^2048 ≤ (5000343527411357/5000000000000000 : ℝ)^8239 := by
      have hnat : (50013821368530832573 : ℕ)^2048*5000000000000000^8239 ≤ 5000343527411357^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013821368530832573 50000000000000000000 5000343527411357 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000343527411357/5000000000000000 : ℝ)) (X := (50013821368530832573/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013304799837859199/25000000000000000000 : ℝ) ≤ (1250165328216021/1250000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (25013304799837859199/25000000000000000000 : ℝ)^2048 ≤ (1250165328216021/1250000000000000 : ℝ)^8239 := by
      have hnat : (25013304799837859199 : ℕ)^2048*1250000000000000^8239 ≤ 1250165328216021^8239*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013304799837859199 25000000000000000000 1250165328216021 1250000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250165328216021/1250000000000000 : ℝ)) (X := (25013304799837859199/25000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039397830820604223/50000000000000000000 : ℝ) ≤ (5000979098316811/5000000000000000 : ℝ) ^ (8239/2048 : ℝ) := by
    have hpowers : (50039397830820604223/50000000000000000000 : ℝ)^2048 ≤ (5000979098316811/5000000000000000 : ℝ)^8239 := by
      have hnat : (50039397830820604223 : ℕ)^2048*5000000000000000^8239 ≤ 5000979098316811^8239*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039397830820604223 50000000000000000000 5000979098316811 5000000000000000 2048 8239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000979098316811/5000000000000000 : ℝ)) (X := (50039397830820604223/50000000000000000000 : ℝ)) (by norm_num) 8239 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13821368530832573/100000000000000000000 : ℝ) ≤ ((4081035689103175397/4082500000000000000 : ℝ)+2*(317785452727/163300000000000 : ℝ)*(10981/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (4081035689103175397/4082500000000000000 : ℝ)+2*(317785452727/163300000000000 : ℝ)*(10981/100000 : ℝ)=(5000343527411357/5000000000000000 : ℝ) by norm_num, show 1+2*(13821368530832573/100000000000000000000 : ℝ)=(50013821368530832573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39397830820604223/100000000000000000000 : ℝ)+(13821368530832573/100000000000000000000 : ℝ) ≤ ((4081035689103175397/4082500000000000000 : ℝ)+(317785452727/163300000000000 : ℝ)*((14247/100000 : ℝ)+(10981/100000 : ℝ)))^(8239/2048 : ℝ) := by
    rw [show (4081035689103175397/4082500000000000000 : ℝ)+(317785452727/163300000000000 : ℝ)*((14247/100000 : ℝ)+(10981/100000 : ℝ))=(1250165328216021/1250000000000000 : ℝ) by norm_num, show 1+(39397830820604223/100000000000000000000 : ℝ)+(13821368530832573/100000000000000000000 : ℝ)=(25013304799837859199/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39397830820604223/100000000000000000000 : ℝ) ≤ ((4081035689103175397/4082500000000000000 : ℝ)+2*(317785452727/163300000000000 : ℝ)*(14247/100000 : ℝ))^(8239/2048 : ℝ) := by
    rw [show (4081035689103175397/4082500000000000000 : ℝ)+2*(317785452727/163300000000000 : ℝ)*(14247/100000 : ℝ)=(5000979098316811/5000000000000000 : ℝ) by norm_num, show 1+2*(39397830820604223/100000000000000000000 : ℝ)=(50039397830820604223/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4081035689103175397/4082500000000000000 : ℝ)*(X 1 0+X 2 0)+(317785452727/163300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (10981/100000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (4081035689103175397/4082500000000000000 : ℝ)) (alpha := (317785452727/163300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4081035689103175397/4082500000000000000 : ℝ)*(X 0 1+X 2 1)+(317785452727/163300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (10981/100000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (4081035689103175397/4082500000000000000 : ℝ)) (alpha := (317785452727/163300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4081035689103175397/4082500000000000000 : ℝ)*(X 0 2+X 1 2)+(317785452727/163300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8239/2048 : ℝ)) (lo := (10981/100000 : ℝ)) (hi := (14247/100000 : ℝ)) (c := (4081035689103175397/4082500000000000000 : ℝ)) (alpha := (317785452727/163300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2212903827/10000000000 : ℝ)*X 0 0+(5397553207/10000000000 : ℝ)*X 0 1+(2630699691/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345733559/10000000000 : ℝ)*X 1 0+(-2282032293/10000000000 : ℝ)*X 1 1+(1052279901/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345733499/10000000000 : ℝ)*X 2 0+(657674947/1250000000 : ℝ)*X 2 1+(-2282032279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((875617357/2000000000 : ℝ)*X 0 0+(530902707/1250000000 : ℝ)*X 0 1+(4513058039/10000000000 : ℝ)*X 0 2+(875617357/2000000000 : ℝ)*X 1 0+(530902707/1250000000 : ℝ)*X 1 1+(4513058039/10000000000 : ℝ)*X 1 2+(875617357/2000000000 : ℝ)*X 2 0+(530902707/1250000000 : ℝ)*X 2 1+(4513058039/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-553227391/2500000000 : ℝ)*X 0 0+(5261754679/10000000000 : ℝ)*X 0 1+(269859831/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311491937/10000000000 : ℝ)*X 1 0+(-2146235041/10000000000 : ℝ)*X 1 1+(5397196619/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265574597/500000000 : ℝ)*X 2 0+(2698598311/5000000000 : ℝ)*X 2 1+(-1073117517/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273631127/625000000 : ℝ)*X 0 0+(2256182219/5000000000 : ℝ)*X 0 1+(530989741/1250000000 : ℝ)*X 0 2+(273631127/625000000 : ℝ)*X 1 0+(2256182219/5000000000 : ℝ)*X 1 1+(530989741/1250000000 : ℝ)*X 1 2+(273631127/625000000 : ℝ)*X 2 0+(2256182219/5000000000 : ℝ)*X 2 1+(530989741/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1047_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (88158292276683768214437/8165000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74688231/4000000000000 : ℝ)*(base19) + (833670569/50000000000000 : ℝ)*(base23) + (62773899/100000000000000 : ℝ)*(lower2) + (295010533/100000000000000 : ℝ)*(upper3) + (212221391/100000000000000 : ℝ)*(upper5) + (2776625424318923/50000000000000 : ℝ)*(major0) + (2776625424318923/50000000000000 : ℝ)*(major1) + (2776625424318923/50000000000000 : ℝ)*(major2) + (7344686686061263/100000000000000 : ℝ)*(sp0) + (7344734902639293/100000000000000 : ℝ)*(sp1) + (734473510250393/10000000000000 : ℝ)*(sp2) + (1880868742925977/50000000000000 : ℝ)*(sp3) + (12520945951/25000000000000 : ℝ)*(sp4) + (27081675447/100000000000000 : ℝ)*(sp7) + (1880882283763701/50000000000000 : ℝ)*(f.failure) + (1836184192461267/25000000000000 : ℝ)*(f.sum) + (19517828325937/8165000000000000000000000000 : ℝ)*base65 + (2912022366271787431/204125000000000000000000000000000 : ℝ)*base67 + (1233125880442662431/204125000000000000000000000000000 : ℝ)*base69 + (1174105550210962569/204125000000000000000000000000000 : ℝ)*base72 + (26340604192477/8165000000000000000000000000 : ℝ)*base73 + (1547097071064287431/204125000000000000000000000000000 : ℝ)*base75 + (1402320828103337569/204125000000000000000000000000000 : ℝ)*base78 + (928547524910587569/204125000000000000000000000000000 : ℝ)*base80 + (30376672811981/4082500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3961481/2500000000000000000000 : ℝ)*base89 + (3961481/2500000000000000000000 : ℝ)*base91 + (3961481/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1108562280526222329955023291/204125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202505091/20000000000000 : ℝ)*(base19) + (554827259/50000000000000 : ℝ)*(base23) + (3505471/3125000000000 : ℝ)*(upper3) + (1261599/3125000000000 : ℝ)*(lower4) + (21755273/20000000000000 : ℝ)*(upper5) + (5582359650205633/100000000000000 : ℝ)*(major0) + (5582359650205633/100000000000000 : ℝ)*(major1) + (5582359650205633/100000000000000 : ℝ)*(major2) + (2600439379/10000000000000 : ℝ)*(sp1) + (14316980477/50000000000000 : ℝ)*(sp2) + (922904536161111/12500000000000 : ℝ)*(sp4) + (7383209272369643/100000000000000 : ℝ)*(sp5) + (922900818209177/12500000000000 : ℝ)*(sp6) + (945370707523917/25000000000000 : ℝ)*(sp7) + (945370707523917/25000000000000 : ℝ)*(f.failure) + (922904536161111/12500000000000 : ℝ)*(f.sum) + (10948660169431/8165000000000000000000000000 : ℝ)*base65 + (1034022302524186301/408250000000000000000000000000000 : ℝ)*base67 + (5289851809668186301/408250000000000000000000000000000 : ℝ)*base69 + (2089172620860936301/408250000000000000000000000000000 : ℝ)*base71 + (8311576616431/2041250000000000000000000000 : ℝ)*base74 + (3929663889510436301/408250000000000000000000000000000 : ℝ)*base75 + (5567545093484686301/408250000000000000000000000000000 : ℝ)*base77 + (1805676324166186301/408250000000000000000000000000000 : ℝ)*base79 + (17046226663819/8165000000000000000000000000 : ℝ)*base82 + (1366177/1250000000000000000000 : ℝ)*base89 + (1366177/1250000000000000000000 : ℝ)*base91 + (1366177/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1047_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10981/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1047_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1047_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4201/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1047_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1047_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1047_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8239/2048 : ℝ) ≤ p) (hpb : p ≤ (515/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73811781/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4201/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4309/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11167/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14051/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1047_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
