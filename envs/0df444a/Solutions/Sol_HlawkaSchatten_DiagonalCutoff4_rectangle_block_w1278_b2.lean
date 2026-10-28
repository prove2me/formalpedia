-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1278_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:22.343682+00:00
-- url     : https://prove2.me/submissions/4810879c-7996-458d-b30d-769c83764d23

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
theorem support_rectangle_w1278_s6_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100570893/10000000000 : ℝ)*x 0 + (541605259/1000000000 : ℝ)*x 1 + (5242380649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100570893/10000000000 : ℝ)^2119 ≤ (12777029228219/100000000000000 : ℝ)^1607 := by
    have hnat : (2100570893 : ℕ)^2119*100000000000000^1607 ≤ 12777029228219^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100570893 10000000000 12777029228219 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541605259/1000000000 : ℝ)^2119 ≤ (2227422571231/5000000000000 : ℝ)^1607 := by
    have hnat : (541605259 : ℕ)^2119*5000000000000^1607 ≤ 2227422571231^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541605259 1000000000 2227422571231 5000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242380649/10000000000 : ℝ)^2119 ≤ (42674519329143/100000000000000 : ℝ)^1607 := by
    have hnat : (5242380649 : ℕ)^2119*100000000000000^1607 ≤ 42674519329143^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242380649 10000000000 42674519329143 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100570893/10000000000 : ℝ), (541605259/1000000000 : ℝ), (5242380649/10000000000 : ℝ)] ![(12777029228219/100000000000000 : ℝ), (2227422571231/5000000000000 : ℝ), (42674519329143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100570893/10000000000 : ℝ)|^2119 ≤ (12777029228219/100000000000000 : ℝ)^1607
        have hw : |(-2100570893/10000000000 : ℝ)|=(2100570893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541605259/1000000000 : ℝ)|^2119 ≤ (2227422571231/5000000000000 : ℝ)^1607
        have hw : |(541605259/1000000000 : ℝ)|=(541605259/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242380649/10000000000 : ℝ)|^2119 ≤ (42674519329143/100000000000000 : ℝ)^1607
        have hw : |(5242380649/10000000000 : ℝ)|=(5242380649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s6_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070002037/2000000000 : ℝ)*x 0 + (-2189113853/10000000000 : ℝ)*x 1 + (655297581/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070002037/2000000000 : ℝ)^2119 ≤ (10958389664561/25000000000000 : ℝ)^1607 := by
    have hnat : (1070002037 : ℕ)^2119*25000000000000^1607 ≤ 10958389664561^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070002037 2000000000 10958389664561 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189113853/10000000000 : ℝ)^2119 ≤ (13491922009509/100000000000000 : ℝ)^1607 := by
    have hnat : (2189113853 : ℕ)^2119*100000000000000^1607 ≤ 13491922009509^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189113853 10000000000 13491922009509 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655297581/1250000000 : ℝ)^2119 ≤ (42674519318409/100000000000000 : ℝ)^1607 := by
    have hnat : (655297581 : ℕ)^2119*100000000000000^1607 ≤ 42674519318409^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655297581 1250000000 42674519318409 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070002037/2000000000 : ℝ), (-2189113853/10000000000 : ℝ), (655297581/1250000000 : ℝ)] ![(10958389664561/25000000000000 : ℝ), (13491922009509/100000000000000 : ℝ), (42674519318409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070002037/2000000000 : ℝ)|^2119 ≤ (10958389664561/25000000000000 : ℝ)^1607
        have hw : |(1070002037/2000000000 : ℝ)|=(1070002037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2189113853/10000000000 : ℝ)|^2119 ≤ (13491922009509/100000000000000 : ℝ)^1607
        have hw : |(-2189113853/10000000000 : ℝ)|=(2189113853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655297581/1250000000 : ℝ)|^2119 ≤ (42674519318409/100000000000000 : ℝ)^1607
        have hw : |(655297581/1250000000 : ℝ)|=(655297581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s6_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1070002037/2000000000 : ℝ)*x 0 + (655297581/1250000000 : ℝ)*x 1 + (-2189113853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070002037/2000000000 : ℝ)^2119 ≤ (10958389664561/25000000000000 : ℝ)^1607 := by
    have hnat : (1070002037 : ℕ)^2119*25000000000000^1607 ≤ 10958389664561^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070002037 2000000000 10958389664561 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655297581/1250000000 : ℝ)^2119 ≤ (42674519318409/100000000000000 : ℝ)^1607 := by
    have hnat : (655297581 : ℕ)^2119*100000000000000^1607 ≤ 42674519318409^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655297581 1250000000 42674519318409 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189113853/10000000000 : ℝ)^2119 ≤ (13491922009509/100000000000000 : ℝ)^1607 := by
    have hnat : (2189113853 : ℕ)^2119*100000000000000^1607 ≤ 13491922009509^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189113853 10000000000 13491922009509 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070002037/2000000000 : ℝ), (655297581/1250000000 : ℝ), (-2189113853/10000000000 : ℝ)] ![(10958389664561/25000000000000 : ℝ), (42674519318409/100000000000000 : ℝ), (13491922009509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070002037/2000000000 : ℝ)|^2119 ≤ (10958389664561/25000000000000 : ℝ)^1607
        have hw : |(1070002037/2000000000 : ℝ)|=(1070002037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655297581/1250000000 : ℝ)|^2119 ≤ (42674519318409/100000000000000 : ℝ)^1607
        have hw : |(655297581/1250000000 : ℝ)|=(655297581/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2189113853/10000000000 : ℝ)|^2119 ≤ (13491922009509/100000000000000 : ℝ)^1607
        have hw : |(-2189113853/10000000000 : ℝ)|=(2189113853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s6_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2171815499/5000000000 : ℝ)*x 0 + (2084803113/5000000000 : ℝ)*x 1 + (904926957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171815499/5000000000 : ℝ)^2119 ≤ (166510130483/500000000000 : ℝ)^1607 := by
    have hnat : (2171815499 : ℕ)^2119*500000000000^1607 ≤ 166510130483^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171815499 5000000000 166510130483 500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2084803113/5000000000 : ℝ)^2119 ≤ (1577702125481/5000000000000 : ℝ)^1607 := by
    have hnat : (2084803113 : ℕ)^2119*5000000000000^1607 ≤ 1577702125481^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084803113 5000000000 1577702125481 5000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904926957/2000000000 : ℝ)^2119 ≤ (35143931381643/100000000000000 : ℝ)^1607 := by
    have hnat : (904926957 : ℕ)^2119*100000000000000^1607 ≤ 35143931381643^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904926957 2000000000 35143931381643 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171815499/5000000000 : ℝ), (2084803113/5000000000 : ℝ), (904926957/2000000000 : ℝ)] ![(166510130483/500000000000 : ℝ), (1577702125481/5000000000000 : ℝ), (35143931381643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171815499/5000000000 : ℝ)|^2119 ≤ (166510130483/500000000000 : ℝ)^1607
        have hw : |(2171815499/5000000000 : ℝ)|=(2171815499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2084803113/5000000000 : ℝ)|^2119 ≤ (1577702125481/5000000000000 : ℝ)^1607
        have hw : |(2084803113/5000000000 : ℝ)|=(2084803113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904926957/2000000000 : ℝ)|^2119 ≤ (35143931381643/100000000000000 : ℝ)^1607
        have hw : |(904926957/2000000000 : ℝ)|=(904926957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s6_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-131286489/625000000 : ℝ)*x 0 + (209719987/400000000 : ℝ)*x 1 + (5415430373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131286489/625000000 : ℝ)^2119 ≤ (12777132942883/100000000000000 : ℝ)^1607 := by
    have hnat : (131286489 : ℕ)^2119*100000000000000^1607 ≤ 12777132942883^1607*625000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131286489 625000000 12777132942883 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209719987/400000000 : ℝ)^2119 ≤ (21340581990457/50000000000000 : ℝ)^1607 := by
    have hnat : (209719987 : ℕ)^2119*50000000000000^1607 ≤ 21340581990457^1607*400000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209719987 400000000 21340581990457 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415430373/10000000000 : ℝ)^2119 ≤ (1113542576421/2500000000000 : ℝ)^1607 := by
    have hnat : (5415430373 : ℕ)^2119*2500000000000^1607 ≤ 1113542576421^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415430373 10000000000 1113542576421 2500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131286489/625000000 : ℝ), (209719987/400000000 : ℝ), (5415430373/10000000000 : ℝ)] ![(12777132942883/100000000000000 : ℝ), (21340581990457/50000000000000 : ℝ), (1113542576421/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131286489/625000000 : ℝ)|^2119 ≤ (12777132942883/100000000000000 : ℝ)^1607
        have hw : |(-131286489/625000000 : ℝ)|=(131286489/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209719987/400000000 : ℝ)|^2119 ≤ (21340581990457/50000000000000 : ℝ)^1607
        have hw : |(209719987/400000000 : ℝ)|=(209719987/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415430373/10000000000 : ℝ)|^2119 ≤ (1113542576421/2500000000000 : ℝ)^1607
        have hw : |(5415430373/10000000000 : ℝ)|=(5415430373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s6_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652812697/5000000000 : ℝ)*x 0 + (-2016064143/10000000000 : ℝ)*x 1 + (5415430373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652812697/5000000000 : ℝ)^2119 ≤ (4335467948891/10000000000000 : ℝ)^1607 := by
    have hnat : (2652812697 : ℕ)^2119*10000000000000^1607 ≤ 4335467948891^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652812697 5000000000 4335467948891 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016064143/10000000000 : ℝ)^2119 ≤ (60518087221/500000000000 : ℝ)^1607 := by
    have hnat : (2016064143 : ℕ)^2119*500000000000^1607 ≤ 60518087221^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016064143 10000000000 60518087221 500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415430373/10000000000 : ℝ)^2119 ≤ (1113542576421/2500000000000 : ℝ)^1607 := by
    have hnat : (5415430373 : ℕ)^2119*2500000000000^1607 ≤ 1113542576421^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415430373 10000000000 1113542576421 2500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652812697/5000000000 : ℝ), (-2016064143/10000000000 : ℝ), (5415430373/10000000000 : ℝ)] ![(4335467948891/10000000000000 : ℝ), (60518087221/500000000000 : ℝ), (1113542576421/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652812697/5000000000 : ℝ)|^2119 ≤ (4335467948891/10000000000000 : ℝ)^1607
        have hw : |(2652812697/5000000000 : ℝ)|=(2652812697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2016064143/10000000000 : ℝ)|^2119 ≤ (60518087221/500000000000 : ℝ)^1607
        have hw : |(-2016064143/10000000000 : ℝ)|=(2016064143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415430373/10000000000 : ℝ)|^2119 ≤ (1113542576421/2500000000000 : ℝ)^1607
        have hw : |(5415430373/10000000000 : ℝ)|=(5415430373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s6_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305625423/10000000000 : ℝ)*x 0 + (2707715173/5000000000 : ℝ)*x 1 + (-2016064139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305625423/10000000000 : ℝ)^2119 ≤ (43354679801383/100000000000000 : ℝ)^1607 := by
    have hnat : (5305625423 : ℕ)^2119*100000000000000^1607 ≤ 43354679801383^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305625423 10000000000 43354679801383 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707715173/5000000000 : ℝ)^2119 ≤ (11135425691003/25000000000000 : ℝ)^1607 := by
    have hnat : (2707715173 : ℕ)^2119*25000000000000^1607 ≤ 11135425691003^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707715173 5000000000 11135425691003 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2016064139/10000000000 : ℝ)^2119 ≤ (6051808706267/50000000000000 : ℝ)^1607 := by
    have hnat : (2016064139 : ℕ)^2119*50000000000000^1607 ≤ 6051808706267^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016064139 10000000000 6051808706267 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305625423/10000000000 : ℝ), (2707715173/5000000000 : ℝ), (-2016064139/10000000000 : ℝ)] ![(43354679801383/100000000000000 : ℝ), (11135425691003/25000000000000 : ℝ), (6051808706267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305625423/10000000000 : ℝ)|^2119 ≤ (43354679801383/100000000000000 : ℝ)^1607
        have hw : |(5305625423/10000000000 : ℝ)|=(5305625423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707715173/5000000000 : ℝ)|^2119 ≤ (11135425691003/25000000000000 : ℝ)^1607
        have hw : |(2707715173/5000000000 : ℝ)|=(2707715173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2016064139/10000000000 : ℝ)|^2119 ≤ (6051808706267/50000000000000 : ℝ)^1607
        have hw : |(-2016064139/10000000000 : ℝ)|=(2016064139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s6_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2171828707/5000000000 : ℝ)*x 0 + (565421163/1250000000 : ℝ)*x 1 + (1042719551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171828707/5000000000 : ℝ)^2119 ≤ (33302293151339/100000000000000 : ℝ)^1607 := by
    have hnat : (2171828707 : ℕ)^2119*100000000000000^1607 ≤ 33302293151339^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171828707 5000000000 33302293151339 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565421163/1250000000 : ℝ)^2119 ≤ (35130970988681/100000000000000 : ℝ)^1607 := by
    have hnat : (565421163 : ℕ)^2119*100000000000000^1607 ≤ 35130970988681^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565421163 1250000000 35130970988681 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042719551/2500000000 : ℝ)^2119 ≤ (6313347168953/20000000000000 : ℝ)^1607 := by
    have hnat : (1042719551 : ℕ)^2119*20000000000000^1607 ≤ 6313347168953^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042719551 2500000000 6313347168953 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171828707/5000000000 : ℝ), (565421163/1250000000 : ℝ), (1042719551/2500000000 : ℝ)] ![(33302293151339/100000000000000 : ℝ), (35130970988681/100000000000000 : ℝ), (6313347168953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171828707/5000000000 : ℝ)|^2119 ≤ (33302293151339/100000000000000 : ℝ)^1607
        have hw : |(2171828707/5000000000 : ℝ)|=(2171828707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565421163/1250000000 : ℝ)|^2119 ≤ (35130970988681/100000000000000 : ℝ)^1607
        have hw : |(565421163/1250000000 : ℝ)|=(565421163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042719551/2500000000 : ℝ)|^2119 ≤ (6313347168953/20000000000000 : ℝ)^1607
        have hw : |(1042719551/2500000000 : ℝ)|=(1042719551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10977/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10989/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2933/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10977/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10977/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10977/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7339/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10977/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10977/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7339/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10977/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10977/100000 : ℝ) ^ (4237/1024 : ℝ) ≤ (10710598883934677/100000000000000000000 : ℝ) := by
    have hpowers : (10977/100000 : ℝ)^4237 ≤ (10710598883934677/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10977 : ℕ)^4237*100000000000000000000^1024 ≤ 10710598883934677^1024*100000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10977 100000 10710598883934677 100000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10977/100000 : ℝ)) (X := (10710598883934677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7339/50000 : ℝ) ^ (4237/1024 : ℝ) ≤ (35638668466844019/100000000000000000000 : ℝ) := by
    have hpowers : (7339/50000 : ℝ)^4237 ≤ (35638668466844019/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7339 : ℕ)^4237*100000000000000000000^1024 ≤ 35638668466844019^1024*50000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7339 50000 35638668466844019 100000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7339/50000 : ℝ)) (X := (35638668466844019/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010710598883934677/50000000000000000000 : ℝ) ≤ (10000517666394617/10000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (50010710598883934677/50000000000000000000 : ℝ)^1024 ≤ (10000517666394617/10000000000000000 : ℝ)^4237 := by
      have hnat : (50010710598883934677 : ℕ)^1024*10000000000000000^4237 ≤ 10000517666394617^4237*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010710598883934677 50000000000000000000 10000517666394617 10000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000517666394617/10000000000000000 : ℝ)) (X := (50010710598883934677/50000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505793658418847337/12500000000000000000 : ℝ) ≤ (10001119974303217/10000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (12505793658418847337/12500000000000000000 : ℝ)^1024 ≤ (10001119974303217/10000000000000000 : ℝ)^4237 := by
      have hnat : (12505793658418847337 : ℕ)^1024*10000000000000000^4237 ≤ 10001119974303217^4237*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505793658418847337 12500000000000000000 10001119974303217 10000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001119974303217/10000000000000000 : ℝ)) (X := (12505793658418847337/12500000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035638668466844019/50000000000000000000 : ℝ) ≤ (10001722282211817/10000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (50035638668466844019/50000000000000000000 : ℝ)^1024 ≤ (10001722282211817/10000000000000000 : ℝ)^4237 := by
      have hnat : (50035638668466844019 : ℕ)^1024*10000000000000000^4237 ≤ 10001722282211817^4237*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035638668466844019 50000000000000000000 10001722282211817 10000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001722282211817/10000000000000000 : ℝ)) (X := (50035638668466844019/50000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10710598883934677/100000000000000000000 : ℝ) ≤ ((36998692815501073117/37010000000000000000 : ℝ)+2*(3011539543/1850500000000 : ℝ)*(10977/100000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (36998692815501073117/37010000000000000000 : ℝ)+2*(3011539543/1850500000000 : ℝ)*(10977/100000 : ℝ)=(10000517666394617/10000000000000000 : ℝ) by norm_num, show 1+2*(10710598883934677/100000000000000000000 : ℝ)=(50010710598883934677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35638668466844019/100000000000000000000 : ℝ)+(10710598883934677/100000000000000000000 : ℝ) ≤ ((36998692815501073117/37010000000000000000 : ℝ)+(3011539543/1850500000000 : ℝ)*((7339/50000 : ℝ)+(10977/100000 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (36998692815501073117/37010000000000000000 : ℝ)+(3011539543/1850500000000 : ℝ)*((7339/50000 : ℝ)+(10977/100000 : ℝ))=(10001119974303217/10000000000000000 : ℝ) by norm_num, show 1+(35638668466844019/100000000000000000000 : ℝ)+(10710598883934677/100000000000000000000 : ℝ)=(12505793658418847337/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35638668466844019/100000000000000000000 : ℝ) ≤ ((36998692815501073117/37010000000000000000 : ℝ)+2*(3011539543/1850500000000 : ℝ)*(7339/50000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (36998692815501073117/37010000000000000000 : ℝ)+2*(3011539543/1850500000000 : ℝ)*(7339/50000 : ℝ)=(10001722282211817/10000000000000000 : ℝ) by norm_num, show 1+2*(35638668466844019/100000000000000000000 : ℝ)=(50035638668466844019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36998692815501073117/37010000000000000000 : ℝ)*(X 1 0+X 2 0)+(3011539543/1850500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10977/100000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (36998692815501073117/37010000000000000000 : ℝ)) (alpha := (3011539543/1850500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36998692815501073117/37010000000000000000 : ℝ)*(X 0 1+X 2 1)+(3011539543/1850500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10977/100000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (36998692815501073117/37010000000000000000 : ℝ)) (alpha := (3011539543/1850500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36998692815501073117/37010000000000000000 : ℝ)*(X 0 2+X 1 2)+(3011539543/1850500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10977/100000 : ℝ)) (hi := (7339/50000 : ℝ)) (c := (36998692815501073117/37010000000000000000 : ℝ)) (alpha := (3011539543/1850500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2100570893/10000000000 : ℝ)*X 0 0+(541605259/1000000000 : ℝ)*X 0 1+(5242380649/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070002037/2000000000 : ℝ)*X 1 0+(-2189113853/10000000000 : ℝ)*X 1 1+(655297581/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070002037/2000000000 : ℝ)*X 2 0+(655297581/1250000000 : ℝ)*X 2 1+(-2189113853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171815499/5000000000 : ℝ)*X 0 0+(2084803113/5000000000 : ℝ)*X 0 1+(904926957/2000000000 : ℝ)*X 0 2+(2171815499/5000000000 : ℝ)*X 1 0+(2084803113/5000000000 : ℝ)*X 1 1+(904926957/2000000000 : ℝ)*X 1 2+(2171815499/5000000000 : ℝ)*X 2 0+(2084803113/5000000000 : ℝ)*X 2 1+(904926957/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-131286489/625000000 : ℝ)*X 0 0+(209719987/400000000 : ℝ)*X 0 1+(5415430373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652812697/5000000000 : ℝ)*X 1 0+(-2016064143/10000000000 : ℝ)*X 1 1+(5415430373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305625423/10000000000 : ℝ)*X 2 0+(2707715173/5000000000 : ℝ)*X 2 1+(-2016064139/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171828707/5000000000 : ℝ)*X 0 0+(565421163/1250000000 : ℝ)*X 0 1+(1042719551/2500000000 : ℝ)*X 0 2+(2171828707/5000000000 : ℝ)*X 1 0+(565421163/1250000000 : ℝ)*X 1 1+(1042719551/2500000000 : ℝ)*X 1 2+(2171828707/5000000000 : ℝ)*X 2 0+(565421163/1250000000 : ℝ)*X 2 1+(1042719551/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35522451383662321604949/3701000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370506229/20000000000000 : ℝ)*(base19) + (862448909/50000000000000 : ℝ)*(base23) + (68283959/100000000000000 : ℝ)*(lower2) + (243213243/100000000000000 : ℝ)*(upper3) + (74040967/50000000000000 : ℝ)*(upper5) + (535923132462941/12500000000000 : ℝ)*(major0) + (535923132462941/12500000000000 : ℝ)*(major1) + (535923132462941/12500000000000 : ℝ)*(major2) + (5758021078504529/100000000000000 : ℝ)*(sp0) + (1439514017353927/25000000000000 : ℝ)*(sp1) + (2879028098524517/50000000000000 : ℝ)*(sp2) + (563338465817103/20000000000000 : ℝ)*(sp3) + (9210860581/25000000000000 : ℝ)*(sp4) + (19548439063/100000000000000 : ℝ)*(sp7) + (1408355938762289/50000000000000 : ℝ)*(f.failure) + (5758057921946853/100000000000000 : ℝ)*(f.sum) + (8525819780181/3701000000000000000000000000 : ℝ)*base65 + (2326223185774857097/462625000000000000000000000000000 : ℝ)*base67 + (1930389694206357097/462625000000000000000000000000000 : ℝ)*base69 + (1376849226185142903/462625000000000000000000000000000 : ℝ)*base72 + (10362120992971/1850500000000000000000000000 : ℝ)*base73 + (3775928969957517903/462625000000000000000000000000000 : ℝ)*base76 + (3248364110223892903/462625000000000000000000000000000 : ℝ)*base78 + (5879983886947107097/462625000000000000000000000000000 : ℝ)*base79 + (1533927238307/740200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (35431221/5000000000000000000000 : ℝ)*base90 + (35431221/5000000000000000000000 : ℝ)*base92 + (35431221/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8641258719647830932249681513/925250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84033661/5000000000000 : ℝ)*(base19) + (923481151/50000000000000 : ℝ)*(base23) + (188601849/100000000000000 : ℝ)*(upper3) + (61320961/100000000000000 : ℝ)*(lower4) + (40306279/20000000000000 : ℝ)*(upper5) + (4318190899422463/100000000000000 : ℝ)*(major0) + (4318190899422463/100000000000000 : ℝ)*(major1) + (4318190899422463/100000000000000 : ℝ)*(major2) + (33627010391/100000000000000 : ℝ)*(sp1) + (35899761297/100000000000000 : ℝ)*(sp2) + (1449857723150477/25000000000000 : ℝ)*(sp4) + (5799395584918297/100000000000000 : ℝ)*(sp5) + (5799393145878309/100000000000000 : ℝ)*(sp6) + (1418475297465219/50000000000000 : ℝ)*(sp7) + (1418475297465219/50000000000000 : ℝ)*(f.failure) + (1449857723150477/25000000000000 : ℝ)*(f.sum) + (659866316361/185050000000000000000000000 : ℝ)*base65 + (48463057267236772829/3701000000000000000000000000000000 : ℝ)*base68 + (36580515578020772829/3701000000000000000000000000000000 : ℝ)*base70 + (25884190212030227171/3701000000000000000000000000000000 : ℝ)*base71 + (12958296156199/1850500000000000000000000000 : ℝ)*base74 + (60968612094985772829/3701000000000000000000000000000000 : ℝ)*base76 + (7366309187568772829/3701000000000000000000000000000000 : ℝ)*base78 + (37528695071706772829/3701000000000000000000000000000000 : ℝ)*base80 + (202779741107/37010000000000000000000000 : ℝ)*base82 + (22633009/5000000000000000000000 : ℝ)*base89 + (22633009/5000000000000000000000 : ℝ)*base91 + (22633009/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1278_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10977/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1278_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1278_s7_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-131286563/625000000 : ℝ)*x 0 + (1353984187/2500000000 : ℝ)*x 1 + (327655447/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131286563/625000000 : ℝ)^2119 ≤ (12777142439309/100000000000000 : ℝ)^1607 := by
    have hnat : (131286563 : ℕ)^2119*100000000000000^1607 ≤ 12777142439309^1607*625000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131286563 625000000 12777142439309 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353984187/2500000000 : ℝ)^2119 ≤ (44547195020401/100000000000000 : ℝ)^1607 := by
    have hnat : (1353984187 : ℕ)^2119*100000000000000^1607 ≤ 44547195020401^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353984187 2500000000 44547195020401 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327655447/625000000 : ℝ)^2119 ≤ (42675662519133/100000000000000 : ℝ)^1607 := by
    have hnat : (327655447 : ℕ)^2119*100000000000000^1607 ≤ 42675662519133^1607*625000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327655447 625000000 42675662519133 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-131286563/625000000 : ℝ), (1353984187/2500000000 : ℝ), (327655447/625000000 : ℝ)] ![(12777142439309/100000000000000 : ℝ), (44547195020401/100000000000000 : ℝ), (42675662519133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-131286563/625000000 : ℝ)|^2119 ≤ (12777142439309/100000000000000 : ℝ)^1607
        have hw : |(-131286563/625000000 : ℝ)|=(131286563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353984187/2500000000 : ℝ)|^2119 ≤ (44547195020401/100000000000000 : ℝ)^1607
        have hw : |(1353984187/2500000000 : ℝ)|=(1353984187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327655447/625000000 : ℝ)|^2119 ≤ (42675662519133/100000000000000 : ℝ)^1607
        have hw : |(327655447/625000000 : ℝ)|=(327655447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s7_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349980509/10000000000 : ℝ)*x 0 + (-2189012639/10000000000 : ℝ)*x 1 + (5242487147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349980509/10000000000 : ℝ)^2119 ≤ (876664761037/2000000000000 : ℝ)^1607 := by
    have hnat : (5349980509 : ℕ)^2119*2000000000000^1607 ≤ 876664761037^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349980509 10000000000 876664761037 2000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2189012639/10000000000 : ℝ)^2119 ≤ (6745549733887/50000000000000 : ℝ)^1607 := by
    have hnat : (2189012639 : ℕ)^2119*50000000000000^1607 ≤ 6745549733887^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189012639 10000000000 6745549733887 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242487147/10000000000 : ℝ)^2119 ≤ (42675662465463/100000000000000 : ℝ)^1607 := by
    have hnat : (5242487147 : ℕ)^2119*100000000000000^1607 ≤ 42675662465463^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242487147 10000000000 42675662465463 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349980509/10000000000 : ℝ), (-2189012639/10000000000 : ℝ), (5242487147/10000000000 : ℝ)] ![(876664761037/2000000000000 : ℝ), (6745549733887/50000000000000 : ℝ), (42675662465463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349980509/10000000000 : ℝ)|^2119 ≤ (876664761037/2000000000000 : ℝ)^1607
        have hw : |(5349980509/10000000000 : ℝ)|=(5349980509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2189012639/10000000000 : ℝ)|^2119 ≤ (6745549733887/50000000000000 : ℝ)^1607
        have hw : |(-2189012639/10000000000 : ℝ)|=(2189012639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242487147/10000000000 : ℝ)|^2119 ≤ (42675662465463/100000000000000 : ℝ)^1607
        have hw : |(5242487147/10000000000 : ℝ)|=(5242487147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s7_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5349980563/10000000000 : ℝ)*x 0 + (81913859/156250000 : ℝ)*x 1 + (-273626599/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349980563/10000000000 : ℝ)^2119 ≤ (43833238635241/100000000000000 : ℝ)^1607 := by
    have hnat : (5349980563 : ℕ)^2119*100000000000000^1607 ≤ 43833238635241^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349980563 10000000000 43833238635241 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81913859/156250000 : ℝ)^2119 ≤ (8535132125993/20000000000000 : ℝ)^1607 := by
    have hnat : (81913859 : ℕ)^2119*20000000000000^1607 ≤ 8535132125993^1607*156250000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81913859 156250000 8535132125993 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273626599/1250000000 : ℝ)^2119 ≤ (13491100711159/100000000000000 : ℝ)^1607 := by
    have hnat : (273626599 : ℕ)^2119*100000000000000^1607 ≤ 13491100711159^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273626599 1250000000 13491100711159 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349980563/10000000000 : ℝ), (81913859/156250000 : ℝ), (-273626599/1250000000 : ℝ)] ![(43833238635241/100000000000000 : ℝ), (8535132125993/20000000000000 : ℝ), (13491100711159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349980563/10000000000 : ℝ)|^2119 ≤ (43833238635241/100000000000000 : ℝ)^1607
        have hw : |(5349980563/10000000000 : ℝ)|=(5349980563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81913859/156250000 : ℝ)|^2119 ≤ (8535132125993/20000000000000 : ℝ)^1607
        have hw : |(81913859/156250000 : ℝ)|=(81913859/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273626599/1250000000 : ℝ)|^2119 ≤ (13491100711159/100000000000000 : ℝ)^1607
        have hw : |(-273626599/1250000000 : ℝ)|=(273626599/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s7_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (173745549/400000000 : ℝ)*x 0 + (833966513/2000000000 : ℝ)*x 1 + (565550829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173745549/400000000 : ℝ)^2119 ≤ (33302104213293/100000000000000 : ℝ)^1607 := by
    have hnat : (173745549 : ℕ)^2119*100000000000000^1607 ≤ 33302104213293^1607*400000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173745549 400000000 33302104213293 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833966513/2000000000 : ℝ)^2119 ≤ (15778150551867/50000000000000 : ℝ)^1607 := by
    have hnat : (833966513 : ℕ)^2119*50000000000000^1607 ≤ 15778150551867^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833966513 2000000000 15778150551867 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565550829/1250000000 : ℝ)^2119 ≤ (35141594672879/100000000000000 : ℝ)^1607 := by
    have hnat : (565550829 : ℕ)^2119*100000000000000^1607 ≤ 35141594672879^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565550829 1250000000 35141594672879 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(173745549/400000000 : ℝ), (833966513/2000000000 : ℝ), (565550829/1250000000 : ℝ)] ![(33302104213293/100000000000000 : ℝ), (15778150551867/50000000000000 : ℝ), (35141594672879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(173745549/400000000 : ℝ)|^2119 ≤ (33302104213293/100000000000000 : ℝ)^1607
        have hw : |(173745549/400000000 : ℝ)|=(173745549/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(833966513/2000000000 : ℝ)|^2119 ≤ (15778150551867/50000000000000 : ℝ)^1607
        have hw : |(833966513/2000000000 : ℝ)|=(833966513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565550829/1250000000 : ℝ)|^2119 ≤ (35141594672879/100000000000000 : ℝ)^1607
        have hw : |(565550829/1250000000 : ℝ)|=(565550829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s7_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050298989/5000000000 : ℝ)*x 0 + (1310776131/2500000000 : ℝ)*x 1 + (1353829033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050298989/5000000000 : ℝ)^2119 ≤ (12777246467/100000000000 : ℝ)^1607 := by
    have hnat : (1050298989 : ℕ)^2119*100000000000^1607 ≤ 12777246467^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050298989 5000000000 12777246467 100000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310776131/2500000000 : ℝ)^2119 ≤ (8536457891871/20000000000000 : ℝ)^1607 := by
    have hnat : (1310776131 : ℕ)^2119*20000000000000^1607 ≤ 8536457891871^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310776131 2500000000 8536457891871 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353829033/2500000000 : ℝ)^2119 ≤ (44540464062113/100000000000000 : ℝ)^1607 := by
    have hnat : (1353829033 : ℕ)^2119*100000000000000^1607 ≤ 44540464062113^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353829033 2500000000 44540464062113 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050298989/5000000000 : ℝ), (1310776131/2500000000 : ℝ), (1353829033/2500000000 : ℝ)] ![(12777246467/100000000000 : ℝ), (8536457891871/20000000000000 : ℝ), (44540464062113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050298989/5000000000 : ℝ)|^2119 ≤ (12777246467/100000000000 : ℝ)^1607
        have hw : |(-1050298989/5000000000 : ℝ)|=(1050298989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310776131/2500000000 : ℝ)|^2119 ≤ (8536457891871/20000000000000 : ℝ)^1607
        have hw : |(1310776131/2500000000 : ℝ)|=(1310776131/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353829033/2500000000 : ℝ)|^2119 ≤ (44540464062113/100000000000000 : ℝ)^1607
        have hw : |(1353829033/2500000000 : ℝ)|=(1353829033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s7_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305652679/10000000000 : ℝ)*x 0 + (-2016183513/10000000000 : ℝ)*x 1 + (1353829033/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305652679/10000000000 : ℝ)^2119 ≤ (43354973483129/100000000000000 : ℝ)^1607 := by
    have hnat : (5305652679 : ℕ)^2119*100000000000000^1607 ≤ 43354973483129^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305652679 10000000000 43354973483129 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016183513/10000000000 : ℝ)^2119 ≤ (12104562429849/100000000000000 : ℝ)^1607 := by
    have hnat : (2016183513 : ℕ)^2119*100000000000000^1607 ≤ 12104562429849^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016183513 10000000000 12104562429849 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353829033/2500000000 : ℝ)^2119 ≤ (44540464062113/100000000000000 : ℝ)^1607 := by
    have hnat : (1353829033 : ℕ)^2119*100000000000000^1607 ≤ 44540464062113^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353829033 2500000000 44540464062113 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305652679/10000000000 : ℝ), (-2016183513/10000000000 : ℝ), (1353829033/2500000000 : ℝ)] ![(43354973483129/100000000000000 : ℝ), (12104562429849/100000000000000 : ℝ), (44540464062113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305652679/10000000000 : ℝ)|^2119 ≤ (43354973483129/100000000000000 : ℝ)^1607
        have hw : |(5305652679/10000000000 : ℝ)|=(5305652679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2016183513/10000000000 : ℝ)|^2119 ≤ (12104562429849/100000000000000 : ℝ)^1607
        have hw : |(-2016183513/10000000000 : ℝ)|=(2016183513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353829033/2500000000 : ℝ)|^2119 ≤ (44540464062113/100000000000000 : ℝ)^1607
        have hw : |(1353829033/2500000000 : ℝ)|=(1353829033/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s7_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305652677/10000000000 : ℝ)*x 0 + (5415316133/10000000000 : ℝ)*x 1 + (-403236703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305652677/10000000000 : ℝ)^2119 ≤ (43354973461579/100000000000000 : ℝ)^1607 := by
    have hnat : (5305652677 : ℕ)^2119*100000000000000^1607 ≤ 43354973461579^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305652677 10000000000 43354973461579 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415316133/10000000000 : ℝ)^2119 ≤ (22270232036479/50000000000000 : ℝ)^1607 := by
    have hnat : (5415316133 : ℕ)^2119*50000000000000^1607 ≤ 22270232036479^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415316133 10000000000 22270232036479 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403236703/2000000000 : ℝ)^2119 ≤ (6052281222841/50000000000000 : ℝ)^1607 := by
    have hnat : (403236703 : ℕ)^2119*50000000000000^1607 ≤ 6052281222841^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403236703 2000000000 6052281222841 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305652677/10000000000 : ℝ), (5415316133/10000000000 : ℝ), (-403236703/2000000000 : ℝ)] ![(43354973461579/100000000000000 : ℝ), (22270232036479/50000000000000 : ℝ), (6052281222841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305652677/10000000000 : ℝ)|^2119 ≤ (43354973461579/100000000000000 : ℝ)^1607
        have hw : |(5305652677/10000000000 : ℝ)|=(5305652677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415316133/10000000000 : ℝ)|^2119 ≤ (22270232036479/50000000000000 : ℝ)^1607
        have hw : |(5415316133/10000000000 : ℝ)|=(5415316133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-403236703/2000000000 : ℝ)|^2119 ≤ (6052281222841/50000000000000 : ℝ)^1607
        have hw : |(-403236703/2000000000 : ℝ)|=(403236703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s7_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (217183261/500000000 : ℝ)*x 0 + (226157219/500000000 : ℝ)*x 1 + (4171101107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217183261/500000000 : ℝ)^2119 ≤ (16651186033421/50000000000000 : ℝ)^1607 := by
    have hnat : (217183261 : ℕ)^2119*50000000000000^1607 ≤ 16651186033421^1607*500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217183261 500000000 16651186033421 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226157219/500000000 : ℝ)^2119 ≤ (35128667555891/100000000000000 : ℝ)^1607 := by
    have hnat : (226157219 : ℕ)^2119*100000000000000^1607 ≤ 35128667555891^1607*500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226157219 500000000 35128667555891 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171101107/10000000000 : ℝ)^2119 ≤ (493265005743/1562500000000 : ℝ)^1607 := by
    have hnat : (4171101107 : ℕ)^2119*1562500000000^1607 ≤ 493265005743^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171101107 10000000000 493265005743 1562500000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217183261/500000000 : ℝ), (226157219/500000000 : ℝ), (4171101107/10000000000 : ℝ)] ![(16651186033421/50000000000000 : ℝ), (35128667555891/100000000000000 : ℝ), (493265005743/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217183261/500000000 : ℝ)|^2119 ≤ (16651186033421/50000000000000 : ℝ)^1607
        have hw : |(217183261/500000000 : ℝ)|=(217183261/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226157219/500000000 : ℝ)|^2119 ≤ (35128667555891/100000000000000 : ℝ)^1607
        have hw : |(226157219/500000000 : ℝ)|=(226157219/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171101107/10000000000 : ℝ)|^2119 ≤ (493265005743/1562500000000 : ℝ)^1607
        have hw : |(4171101107/10000000000 : ℝ)|=(4171101107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (687/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7331/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2933/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2933/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10989/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2933/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2933/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10989/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2933/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2933/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10989/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10989/100000 : ℝ) ^ (4237/1024 : ℝ) ≤ (10759129368221163/100000000000000000000 : ℝ) := by
    have hpowers : (10989/100000 : ℝ)^4237 ≤ (10759129368221163/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10989 : ℕ)^4237*100000000000000000000^1024 ≤ 10759129368221163^1024*100000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10989 100000 10759129368221163 100000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10989/100000 : ℝ)) (X := (10759129368221163/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2933/20000 : ℝ) ^ (4237/1024 : ℝ) ≤ (17754122917893151/50000000000000000000 : ℝ) := by
    have hpowers : (2933/20000 : ℝ)^4237 ≤ (17754122917893151/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2933 : ℕ)^4237*50000000000000000000^1024 ≤ 17754122917893151^1024*20000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2933 20000 17754122917893151 50000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2933/20000 : ℝ)) (X := (17754122917893151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010759129368221163/50000000000000000000 : ℝ) ≤ (125006500147331/125000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (50010759129368221163/50000000000000000000 : ℝ)^1024 ≤ (125006500147331/125000000000000 : ℝ)^4237 := by
      have hnat : (50010759129368221163 : ℕ)^1024*125000000000000^4237 ≤ 125006500147331^4237*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010759129368221163 50000000000000000000 125006500147331 125000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125006500147331/125000000000000 : ℝ)) (X := (50010759129368221163/50000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009253475040801493/20000000000000000000 : ℝ) ≤ (10001117995824991/10000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (20009253475040801493/20000000000000000000 : ℝ)^1024 ≤ (10001117995824991/10000000000000000 : ℝ)^4237 := by
      have hnat : (20009253475040801493 : ℕ)^1024*10000000000000000^4237 ≤ 10001117995824991^4237*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009253475040801493 20000000000000000000 10001117995824991 10000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001117995824991/10000000000000000 : ℝ)) (X := (20009253475040801493/20000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017754122917893151/25000000000000000000 : ℝ) ≤ (5000857989931751/5000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (25017754122917893151/25000000000000000000 : ℝ)^1024 ≤ (5000857989931751/5000000000000000 : ℝ)^4237 := by
      have hnat : (25017754122917893151 : ℕ)^1024*5000000000000000^4237 ≤ 5000857989931751^4237*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017754122917893151 25000000000000000000 5000857989931751 5000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000857989931751/5000000000000000 : ℝ)) (X := (25017754122917893151/25000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10759129368221163/100000000000000000000 : ℝ) ≤ ((18374384535064352861/18380000000000000000 : ℝ)+2*(597984038511/367600000000000 : ℝ)*(10989/100000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (18374384535064352861/18380000000000000000 : ℝ)+2*(597984038511/367600000000000 : ℝ)*(10989/100000 : ℝ)=(125006500147331/125000000000000 : ℝ) by norm_num, show 1+2*(10759129368221163/100000000000000000000 : ℝ)=(50010759129368221163/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17754122917893151/50000000000000000000 : ℝ)+(10759129368221163/100000000000000000000 : ℝ) ≤ ((18374384535064352861/18380000000000000000 : ℝ)+(597984038511/367600000000000 : ℝ)*((2933/20000 : ℝ)+(10989/100000 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (18374384535064352861/18380000000000000000 : ℝ)+(597984038511/367600000000000 : ℝ)*((2933/20000 : ℝ)+(10989/100000 : ℝ))=(10001117995824991/10000000000000000 : ℝ) by norm_num, show 1+(17754122917893151/50000000000000000000 : ℝ)+(10759129368221163/100000000000000000000 : ℝ)=(20009253475040801493/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17754122917893151/50000000000000000000 : ℝ) ≤ ((18374384535064352861/18380000000000000000 : ℝ)+2*(597984038511/367600000000000 : ℝ)*(2933/20000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (18374384535064352861/18380000000000000000 : ℝ)+2*(597984038511/367600000000000 : ℝ)*(2933/20000 : ℝ)=(5000857989931751/5000000000000000 : ℝ) by norm_num, show 1+2*(17754122917893151/50000000000000000000 : ℝ)=(25017754122917893151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18374384535064352861/18380000000000000000 : ℝ)*(X 1 0+X 2 0)+(597984038511/367600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (2933/20000 : ℝ)) (c := (18374384535064352861/18380000000000000000 : ℝ)) (alpha := (597984038511/367600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18374384535064352861/18380000000000000000 : ℝ)*(X 0 1+X 2 1)+(597984038511/367600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (2933/20000 : ℝ)) (c := (18374384535064352861/18380000000000000000 : ℝ)) (alpha := (597984038511/367600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18374384535064352861/18380000000000000000 : ℝ)*(X 0 2+X 1 2)+(597984038511/367600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10989/100000 : ℝ)) (hi := (2933/20000 : ℝ)) (c := (18374384535064352861/18380000000000000000 : ℝ)) (alpha := (597984038511/367600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-131286563/625000000 : ℝ)*X 0 0+(1353984187/2500000000 : ℝ)*X 0 1+(327655447/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349980509/10000000000 : ℝ)*X 1 0+(-2189012639/10000000000 : ℝ)*X 1 1+(5242487147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349980563/10000000000 : ℝ)*X 2 0+(81913859/156250000 : ℝ)*X 2 1+(-273626599/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((173745549/400000000 : ℝ)*X 0 0+(833966513/2000000000 : ℝ)*X 0 1+(565550829/1250000000 : ℝ)*X 0 2+(173745549/400000000 : ℝ)*X 1 0+(833966513/2000000000 : ℝ)*X 1 1+(565550829/1250000000 : ℝ)*X 1 2+(173745549/400000000 : ℝ)*X 2 0+(833966513/2000000000 : ℝ)*X 2 1+(565550829/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1050298989/5000000000 : ℝ)*X 0 0+(1310776131/2500000000 : ℝ)*X 0 1+(1353829033/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305652679/10000000000 : ℝ)*X 1 0+(-2016183513/10000000000 : ℝ)*X 1 1+(1353829033/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305652677/10000000000 : ℝ)*X 2 0+(5415316133/10000000000 : ℝ)*X 2 1+(-403236703/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((217183261/500000000 : ℝ)*X 0 0+(226157219/500000000 : ℝ)*X 0 1+(4171101107/10000000000 : ℝ)*X 0 2+(217183261/500000000 : ℝ)*X 1 0+(226157219/500000000 : ℝ)*X 1 1+(4171101107/10000000000 : ℝ)*X 1 2+(217183261/500000000 : ℝ)*X 2 0+(226157219/500000000 : ℝ)*X 2 1+(4171101107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1815559219074406549310012253/459500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35577229/25000000000000 : ℝ)*(base19) + (122011437/50000000000000 : ℝ)*(base23) + (47508593/100000000000000 : ℝ)*(upper3) + (4181293/12500000000000 : ℝ)*(lower4) + (2146413886143509/50000000000000 : ℝ)*(major0) + (2146413886143509/50000000000000 : ℝ)*(major1) + (2146413886143509/50000000000000 : ℝ)*(major2) + (1441341699638449/25000000000000 : ℝ)*(sp0) + (5765367657950353/100000000000000 : ℝ)*(sp1) + (2882682631372711/50000000000000 : ℝ)*(sp2) + (705071527796123/25000000000000 : ℝ)*(sp3) + (1001705473/100000000000000 : ℝ)*(sp4) + (2293490973/100000000000000 : ℝ)*(sp6) + (1501424849/100000000000000 : ℝ)*(sp7) + (2820287612609341/100000000000000 : ℝ)*(f.failure) + (5765367800259269/100000000000000 : ℝ)*(f.sum) + (2930439285321/9190000000000000000000000000 : ℝ)*base66 + (3793497843524320751/919000000000000000000000000000000 : ℝ)*base68 + (8049064832230679249/919000000000000000000000000000000 : ℝ)*base69 + (7253935638467320751/919000000000000000000000000000000 : ℝ)*base72 + (8798148738171/9190000000000000000000000000 : ℝ)*base74 + (14660173039733679249/919000000000000000000000000000000 : ℝ)*base75 + (2992594889562679249/919000000000000000000000000000000 : ℝ)*base77 + (9438047253176679249/919000000000000000000000000000000 : ℝ)*base79 + (24425205525821/9190000000000000000000000000 : ℝ)*base82 + (5268849/10000000000000000000000 : ℝ)*base90 + (5268849/10000000000000000000000 : ℝ)*base92 + (5268849/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34575295445896408680027/9190000000000000000000000000 : ℝ) := by norm_num
    linear_combination (677512061/100000000000000 : ℝ)*(base19) + (733815923/100000000000000 : ℝ)*(base23) + (23428419/10000000000000 : ℝ)*(lower1) + (76333669/100000000000000 : ℝ)*(upper3) + (13399153/50000000000000 : ℝ)*(lower4) + (19261873/25000000000000 : ℝ)*(upper5) + (2161837128423931/50000000000000 : ℝ)*(major0) + (2161837128423931/50000000000000 : ℝ)*(major1) + (2161837128423931/50000000000000 : ℝ)*(major2) + (955589197/100000000000000 : ℝ)*(sp2) + (2903397677779637/50000000000000 : ℝ)*(sp4) + (5806794678047213/100000000000000 : ℝ)*(sp5) + (2903396833077077/50000000000000 : ℝ)*(sp6) + (177534564545457/6250000000000 : ℝ)*(sp7) + (177534564545457/6250000000000 : ℝ)*(f.failure) + (2903397677779637/50000000000000 : ℝ)*(f.sum) + (29790933267821/9190000000000000000000000000 : ℝ)*base65 + (3453692286733766591/919000000000000000000000000000000 : ℝ)*base67 + (1325490084429766591/919000000000000000000000000000000 : ℝ)*base69 + (7202167973655233409/919000000000000000000000000000000 : ℝ)*base72 + (42618642002451/9190000000000000000000000000 : ℝ)*base73 + (22974829175782233409/919000000000000000000000000000000 : ℝ)*base76 + (7974552262246766591/919000000000000000000000000000000 : ℝ)*base77 + (12941643747848233409/919000000000000000000000000000000 : ℝ)*base80 + (49094320902759/9190000000000000000000000000 : ℝ)*base82 + (8433173/625000000000000000000 : ℝ)*base90 + (8433173/625000000000000000000 : ℝ)*base92 + (8433173/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1278_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2933/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10989/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1278_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1278_box_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1928050871/10000000000 : ℝ)*x 0 + (5392586487/10000000000 : ℝ)*x 1 + (5392586487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928050871/10000000000 : ℝ)^2119 ≤ (11411766564317/100000000000000 : ℝ)^1607 := by
    have hnat : (1928050871 : ℕ)^2119*100000000000000^1607 ≤ 11411766564317^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928050871 10000000000 11411766564317 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392586487/10000000000 : ℝ)^2119 ≤ (4429411671261/10000000000000 : ℝ)^1607 := by
    have hnat : (5392586487 : ℕ)^2119*10000000000000^1607 ≤ 4429411671261^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392586487 10000000000 4429411671261 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392586487/10000000000 : ℝ)^2119 ≤ (4429411671261/10000000000000 : ℝ)^1607 := by
    have hnat : (5392586487 : ℕ)^2119*10000000000000^1607 ≤ 4429411671261^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392586487 10000000000 4429411671261 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1928050871/10000000000 : ℝ), (5392586487/10000000000 : ℝ), (5392586487/10000000000 : ℝ)] ![(11411766564317/100000000000000 : ℝ), (4429411671261/10000000000000 : ℝ), (4429411671261/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1928050871/10000000000 : ℝ)|^2119 ≤ (11411766564317/100000000000000 : ℝ)^1607
        have hw : |(-1928050871/10000000000 : ℝ)|=(1928050871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392586487/10000000000 : ℝ)|^2119 ≤ (4429411671261/10000000000000 : ℝ)^1607
        have hw : |(5392586487/10000000000 : ℝ)|=(5392586487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392586487/10000000000 : ℝ)|^2119 ≤ (4429411671261/10000000000000 : ℝ)^1607
        have hw : |(5392586487/10000000000 : ℝ)|=(5392586487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (264205297/500000000 : ℝ)*x 0 + (-2076325671/10000000000 : ℝ)*x 1 + (5392586329/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264205297/500000000 : ℝ)^2119 ≤ (10780739706137/25000000000000 : ℝ)^1607 := by
    have hnat : (264205297 : ℕ)^2119*25000000000000^1607 ≤ 10780739706137^1607*500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264205297 500000000 10780739706137 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076325671/10000000000 : ℝ)^2119 ≤ (1258292615733/10000000000000 : ℝ)^1607 := by
    have hnat : (2076325671 : ℕ)^2119*10000000000000^1607 ≤ 1258292615733^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076325671 10000000000 1258292615733 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392586329/10000000000 : ℝ)^2119 ≤ (4429411500133/10000000000000 : ℝ)^1607 := by
    have hnat : (5392586329 : ℕ)^2119*10000000000000^1607 ≤ 4429411500133^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392586329 10000000000 4429411500133 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264205297/500000000 : ℝ), (-2076325671/10000000000 : ℝ), (5392586329/10000000000 : ℝ)] ![(10780739706137/25000000000000 : ℝ), (1258292615733/10000000000000 : ℝ), (4429411500133/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264205297/500000000 : ℝ)|^2119 ≤ (10780739706137/25000000000000 : ℝ)^1607
        have hw : |(264205297/500000000 : ℝ)|=(264205297/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076325671/10000000000 : ℝ)|^2119 ≤ (1258292615733/10000000000000 : ℝ)^1607
        have hw : |(-2076325671/10000000000 : ℝ)|=(2076325671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392586329/10000000000 : ℝ)|^2119 ≤ (4429411500133/10000000000000 : ℝ)^1607
        have hw : |(5392586329/10000000000 : ℝ)|=(5392586329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5284105737/10000000000 : ℝ)*x 0 + (337036641/625000000 : ℝ)*x 1 + (-2076326043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284105737/10000000000 : ℝ)^2119 ≤ (43122956640067/100000000000000 : ℝ)^1607 := by
    have hnat : (5284105737 : ℕ)^2119*100000000000000^1607 ≤ 43122956640067^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284105737 10000000000 43122956640067 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337036641/625000000 : ℝ)^2119 ≤ (1771764568427/4000000000000 : ℝ)^1607 := by
    have hnat : (337036641 : ℕ)^2119*4000000000000^1607 ≤ 1771764568427^1607*625000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337036641 625000000 1771764568427 4000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076326043/10000000000 : ℝ)^2119 ≤ (12582929129983/100000000000000 : ℝ)^1607 := by
    have hnat : (2076326043 : ℕ)^2119*100000000000000^1607 ≤ 12582929129983^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076326043 10000000000 12582929129983 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284105737/10000000000 : ℝ), (337036641/625000000 : ℝ), (-2076326043/10000000000 : ℝ)] ![(43122956640067/100000000000000 : ℝ), (1771764568427/4000000000000 : ℝ), (12582929129983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284105737/10000000000 : ℝ)|^2119 ≤ (43122956640067/100000000000000 : ℝ)^1607
        have hw : |(5284105737/10000000000 : ℝ)|=(5284105737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337036641/625000000 : ℝ)|^2119 ≤ (1771764568427/4000000000000 : ℝ)^1607
        have hw : |(337036641/625000000 : ℝ)|=(337036641/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2076326043/10000000000 : ℝ)|^2119 ≤ (12582929129983/100000000000000 : ℝ)^1607
        have hw : |(-2076326043/10000000000 : ℝ)|=(2076326043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4493432671/10000000000 : ℝ)*x 0 + (2136391113/5000000000 : ℝ)*x 1 + (4272782257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493432671/10000000000 : ℝ)^2119 ≤ (4353089133449/12500000000000 : ℝ)^1607 := by
    have hnat : (4493432671 : ℕ)^2119*12500000000000^1607 ≤ 4353089133449^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493432671 10000000000 4353089133449 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136391113/5000000000 : ℝ)^2119 ≤ (32587643301413/100000000000000 : ℝ)^1607 := by
    have hnat : (2136391113 : ℕ)^2119*100000000000000^1607 ≤ 32587643301413^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136391113 5000000000 32587643301413 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4272782257/10000000000 : ℝ)^2119 ≤ (8146910903293/25000000000000 : ℝ)^1607 := by
    have hnat : (4272782257 : ℕ)^2119*25000000000000^1607 ≤ 8146910903293^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272782257 10000000000 8146910903293 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493432671/10000000000 : ℝ), (2136391113/5000000000 : ℝ), (4272782257/10000000000 : ℝ)] ![(4353089133449/12500000000000 : ℝ), (32587643301413/100000000000000 : ℝ), (8146910903293/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493432671/10000000000 : ℝ)|^2119 ≤ (4353089133449/12500000000000 : ℝ)^1607
        have hw : |(4493432671/10000000000 : ℝ)|=(4493432671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2136391113/5000000000 : ℝ)|^2119 ≤ (32587643301413/100000000000000 : ℝ)^1607
        have hw : |(2136391113/5000000000 : ℝ)|=(2136391113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4272782257/10000000000 : ℝ)|^2119 ≤ (8146910903293/25000000000000 : ℝ)^1607
        have hw : |(4272782257/10000000000 : ℝ)|=(4272782257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1137942131/5000000000 : ℝ)*x 0 + (2631651839/5000000000 : ℝ)*x 1 + (1052660819/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1137942131/5000000000 : ℝ)^2119 ≤ (14201502589827/100000000000000 : ℝ)^1607 := by
    have hnat : (1137942131 : ℕ)^2119*100000000000000^1607 ≤ 14201502589827^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137942131 5000000000 14201502589827 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631651839/5000000000 : ℝ)^2119 ≤ (10724811615357/25000000000000 : ℝ)^1607 := by
    have hnat : (2631651839 : ℕ)^2119*25000000000000^1607 ≤ 10724811615357^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631651839 5000000000 10724811615357 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052660819/2000000000 : ℝ)^2119 ≤ (10724812735781/25000000000000 : ℝ)^1607 := by
    have hnat : (1052660819 : ℕ)^2119*25000000000000^1607 ≤ 10724812735781^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052660819 2000000000 10724812735781 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1137942131/5000000000 : ℝ), (2631651839/5000000000 : ℝ), (1052660819/2000000000 : ℝ)] ![(14201502589827/100000000000000 : ℝ), (10724811615357/25000000000000 : ℝ), (10724812735781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1137942131/5000000000 : ℝ)|^2119 ≤ (14201502589827/100000000000000 : ℝ)^1607
        have hw : |(-1137942131/5000000000 : ℝ)|=(1137942131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631651839/5000000000 : ℝ)|^2119 ≤ (10724811615357/25000000000000 : ℝ)^1607
        have hw : |(2631651839/5000000000 : ℝ)|=(2631651839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052660819/2000000000 : ℝ)|^2119 ≤ (10724812735781/25000000000000 : ℝ)^1607
        have hw : |(1052660819/2000000000 : ℝ)|=(1052660819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1343790203/2500000000 : ℝ)*x 0 + (-2127725331/10000000000 : ℝ)*x 1 + (5263303993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343790203/2500000000 : ℝ)^2119 ≤ (44105478431273/100000000000000 : ℝ)^1607 := by
    have hnat : (1343790203 : ℕ)^2119*100000000000000^1607 ≤ 44105478431273^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343790203 2500000000 44105478431273 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127725331/10000000000 : ℝ)^2119 ≤ (12995271702481/100000000000000 : ℝ)^1607 := by
    have hnat : (2127725331 : ℕ)^2119*100000000000000^1607 ≤ 12995271702481^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127725331 10000000000 12995271702481 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263303993/10000000000 : ℝ)^2119 ≤ (21449624923441/50000000000000 : ℝ)^1607 := by
    have hnat : (5263303993 : ℕ)^2119*50000000000000^1607 ≤ 21449624923441^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263303993 10000000000 21449624923441 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343790203/2500000000 : ℝ), (-2127725331/10000000000 : ℝ), (5263303993/10000000000 : ℝ)] ![(44105478431273/100000000000000 : ℝ), (12995271702481/100000000000000 : ℝ), (21449624923441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343790203/2500000000 : ℝ)|^2119 ≤ (44105478431273/100000000000000 : ℝ)^1607
        have hw : |(1343790203/2500000000 : ℝ)|=(1343790203/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2127725331/10000000000 : ℝ)|^2119 ≤ (12995271702481/100000000000000 : ℝ)^1607
        have hw : |(-2127725331/10000000000 : ℝ)|=(2127725331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263303993/10000000000 : ℝ)|^2119 ≤ (21449624923441/50000000000000 : ℝ)^1607
        have hw : |(5263303993/10000000000 : ℝ)|=(5263303993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (671895151/1250000000 : ℝ)*x 0 + (5263303661/10000000000 : ℝ)*x 1 + (-1063862621/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671895151/1250000000 : ℝ)^2119 ≤ (44105482715883/100000000000000 : ℝ)^1607 := by
    have hnat : (671895151 : ℕ)^2119*100000000000000^1607 ≤ 44105482715883^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671895151 1250000000 44105482715883 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263303661/10000000000 : ℝ)^2119 ≤ (42899246278721/100000000000000 : ℝ)^1607 := by
    have hnat : (5263303661 : ℕ)^2119*100000000000000^1607 ≤ 42899246278721^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263303661 10000000000 42899246278721 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063862621/5000000000 : ℝ)^2119 ≤ (12995270985719/100000000000000 : ℝ)^1607 := by
    have hnat : (1063862621 : ℕ)^2119*100000000000000^1607 ≤ 12995270985719^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063862621 5000000000 12995270985719 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671895151/1250000000 : ℝ), (5263303661/10000000000 : ℝ), (-1063862621/5000000000 : ℝ)] ![(44105482715883/100000000000000 : ℝ), (42899246278721/100000000000000 : ℝ), (12995270985719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671895151/1250000000 : ℝ)|^2119 ≤ (44105482715883/100000000000000 : ℝ)^1607
        have hw : |(671895151/1250000000 : ℝ)|=(671895151/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263303661/10000000000 : ℝ)|^2119 ≤ (42899246278721/100000000000000 : ℝ)^1607
        have hw : |(5263303661/10000000000 : ℝ)|=(5263303661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1063862621/5000000000 : ℝ)|^2119 ≤ (12995270985719/100000000000000 : ℝ)^1607
        have hw : |(-1063862621/5000000000 : ℝ)|=(1063862621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (524127221/1250000000 : ℝ)*x 0 + (2211466993/5000000000 : ℝ)*x 1 + (4422933617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524127221/1250000000 : ℝ)^2119 ≤ (7946967134503/25000000000000 : ℝ)^1607 := by
    have hnat : (524127221 : ℕ)^2119*25000000000000^1607 ≤ 7946967134503^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524127221 1250000000 7946967134503 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211466993/5000000000 : ℝ)^2119 ≤ (17053033801813/50000000000000 : ℝ)^1607 := by
    have hnat : (2211466993 : ℕ)^2119*50000000000000^1607 ≤ 17053033801813^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211466993 5000000000 17053033801813 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4422933617/10000000000 : ℝ)^2119 ≤ (8526515962907/25000000000000 : ℝ)^1607 := by
    have hnat : (4422933617 : ℕ)^2119*25000000000000^1607 ≤ 8526515962907^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422933617 10000000000 8526515962907 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524127221/1250000000 : ℝ), (2211466993/5000000000 : ℝ), (4422933617/10000000000 : ℝ)] ![(7946967134503/25000000000000 : ℝ), (17053033801813/50000000000000 : ℝ), (8526515962907/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524127221/1250000000 : ℝ)|^2119 ≤ (7946967134503/25000000000000 : ℝ)^1607
        have hw : |(524127221/1250000000 : ℝ)|=(524127221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2211466993/5000000000 : ℝ)|^2119 ≤ (17053033801813/50000000000000 : ℝ)^1607
        have hw : |(2211466993/5000000000 : ℝ)|=(2211466993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4422933617/10000000000 : ℝ)|^2119 ≤ (8526515962907/25000000000000 : ℝ)^1607
        have hw : |(4422933617/10000000000 : ℝ)|=(4422933617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_8 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2203024061/10000000000 : ℝ)*x 0 + (5174616063/10000000000 : ℝ)*x 1 + (5406628823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2203024061/10000000000 : ℝ)^2119 ≤ (13605082009439/100000000000000 : ℝ)^1607 := by
    have hnat : (2203024061 : ℕ)^2119*100000000000000^1607 ≤ 13605082009439^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2203024061 10000000000 13605082009439 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174616063/10000000000 : ℝ)^2119 ≤ (41948647253643/100000000000000 : ℝ)^1607 := by
    have hnat : (5174616063 : ℕ)^2119*100000000000000^1607 ≤ 41948647253643^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174616063 10000000000 41948647253643 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406628823/10000000000 : ℝ)^2119 ≤ (4444627071469/10000000000000 : ℝ)^1607 := by
    have hnat : (5406628823 : ℕ)^2119*10000000000000^1607 ≤ 4444627071469^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406628823 10000000000 4444627071469 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2203024061/10000000000 : ℝ), (5174616063/10000000000 : ℝ), (5406628823/10000000000 : ℝ)] ![(13605082009439/100000000000000 : ℝ), (41948647253643/100000000000000 : ℝ), (4444627071469/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2203024061/10000000000 : ℝ)|^2119 ≤ (13605082009439/100000000000000 : ℝ)^1607
        have hw : |(-2203024061/10000000000 : ℝ)|=(2203024061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174616063/10000000000 : ℝ)|^2119 ≤ (41948647253643/100000000000000 : ℝ)^1607
        have hw : |(5174616063/10000000000 : ℝ)|=(5174616063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406628823/10000000000 : ℝ)|^2119 ≤ (4444627071469/10000000000000 : ℝ)^1607
        have hw : |(5406628823/10000000000 : ℝ)|=(5406628823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_9 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2637104791/5000000000 : ℝ)*x 0 + (-517651527/2500000000 : ℝ)*x 1 + (540662809/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637104791/5000000000 : ℝ)^2119 ≤ (21508248014461/50000000000000 : ℝ)^1607 := by
    have hnat : (2637104791 : ℕ)^2119*50000000000000^1607 ≤ 21508248014461^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637104791 5000000000 21508248014461 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517651527/2500000000 : ℝ)^2119 ≤ (12537241185453/100000000000000 : ℝ)^1607 := by
    have hnat : (517651527 : ℕ)^2119*100000000000000^1607 ≤ 12537241185453^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517651527 2500000000 12537241185453 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540662809/1000000000 : ℝ)^2119 ≤ (44446262769069/100000000000000 : ℝ)^1607 := by
    have hnat : (540662809 : ℕ)^2119*100000000000000^1607 ≤ 44446262769069^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540662809 1000000000 44446262769069 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637104791/5000000000 : ℝ), (-517651527/2500000000 : ℝ), (540662809/1000000000 : ℝ)] ![(21508248014461/50000000000000 : ℝ), (12537241185453/100000000000000 : ℝ), (44446262769069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637104791/5000000000 : ℝ)|^2119 ≤ (21508248014461/50000000000000 : ℝ)^1607
        have hw : |(2637104791/5000000000 : ℝ)|=(2637104791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517651527/2500000000 : ℝ)|^2119 ≤ (12537241185453/100000000000000 : ℝ)^1607
        have hw : |(-517651527/2500000000 : ℝ)|=(517651527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540662809/1000000000 : ℝ)|^2119 ≤ (44446262769069/100000000000000 : ℝ)^1607
        have hw : |(540662809/1000000000 : ℝ)|=(540662809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_10 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5274209753/10000000000 : ℝ)*x 0 + (5406628171/10000000000 : ℝ)*x 1 + (-258825721/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274209753/10000000000 : ℝ)^2119 ≤ (2688531116747/6250000000000 : ℝ)^1607 := by
    have hnat : (5274209753 : ℕ)^2119*6250000000000^1607 ≤ 2688531116747^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274209753 10000000000 2688531116747 6250000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406628171/10000000000 : ℝ)^2119 ≤ (22223131823549/50000000000000 : ℝ)^1607 := by
    have hnat : (5406628171 : ℕ)^2119*50000000000000^1607 ≤ 22223131823549^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406628171 10000000000 22223131823549 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258825721/1250000000 : ℝ)^2119 ≤ (12537238470899/100000000000000 : ℝ)^1607 := by
    have hnat : (258825721 : ℕ)^2119*100000000000000^1607 ≤ 12537238470899^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258825721 1250000000 12537238470899 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274209753/10000000000 : ℝ), (5406628171/10000000000 : ℝ), (-258825721/1250000000 : ℝ)] ![(2688531116747/6250000000000 : ℝ), (22223131823549/50000000000000 : ℝ), (12537238470899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274209753/10000000000 : ℝ)|^2119 ≤ (2688531116747/6250000000000 : ℝ)^1607
        have hw : |(5274209753/10000000000 : ℝ)|=(5274209753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406628171/10000000000 : ℝ)|^2119 ≤ (22223131823549/50000000000000 : ℝ)^1607
        have hw : |(5406628171/10000000000 : ℝ)|=(5406628171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258825721/1250000000 : ℝ)|^2119 ≤ (12537238470899/100000000000000 : ℝ)^1607
        have hw : |(-258825721/1250000000 : ℝ)|=(258825721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_11 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2262750951/5000000000 : ℝ)*x 0 + (425646047/1000000000 : ℝ)*x 1 + (2128229647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2262750951/5000000000 : ℝ)^2119 ≤ (35152812606197/100000000000000 : ℝ)^1607 := by
    have hnat : (2262750951 : ℕ)^2119*100000000000000^1607 ≤ 35152812606197^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262750951 5000000000 35152812606197 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425646047/1000000000 : ℝ)^2119 ≤ (2026474974851/6250000000000 : ℝ)^1607 := by
    have hnat : (425646047 : ℕ)^2119*6250000000000^1607 ≤ 2026474974851^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425646047 1000000000 2026474974851 6250000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128229647/5000000000 : ℝ)^2119 ≤ (32423587785301/100000000000000 : ℝ)^1607 := by
    have hnat : (2128229647 : ℕ)^2119*100000000000000^1607 ≤ 32423587785301^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128229647 5000000000 32423587785301 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2262750951/5000000000 : ℝ), (425646047/1000000000 : ℝ), (2128229647/5000000000 : ℝ)] ![(35152812606197/100000000000000 : ℝ), (2026474974851/6250000000000 : ℝ), (32423587785301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2262750951/5000000000 : ℝ)|^2119 ≤ (35152812606197/100000000000000 : ℝ)^1607
        have hw : |(2262750951/5000000000 : ℝ)|=(2262750951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425646047/1000000000 : ℝ)|^2119 ≤ (2026474974851/6250000000000 : ℝ)^1607
        have hw : |(425646047/1000000000 : ℝ)|=(425646047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2128229647/5000000000 : ℝ)|^2119 ≤ (32423587785301/100000000000000 : ℝ)^1607
        have hw : |(2128229647/5000000000 : ℝ)|=(2128229647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_12 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001380269/10000000000 : ℝ)*x 0 + (219156617/400000000 : ℝ)*x 1 + (5252295779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001380269/10000000000 : ℝ)^2119 ≤ (2996877401289/25000000000000 : ℝ)^1607 := by
    have hnat : (2001380269 : ℕ)^2119*25000000000000^1607 ≤ 2996877401289^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001380269 10000000000 2996877401289 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219156617/400000000 : ℝ)^2119 ≤ (9046302313667/20000000000000 : ℝ)^1607 := by
    have hnat : (219156617 : ℕ)^2119*20000000000000^1607 ≤ 9046302313667^1607*400000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219156617 400000000 9046302313667 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252295779/10000000000 : ℝ)^2119 ≤ (42780978812543/100000000000000 : ℝ)^1607 := by
    have hnat : (5252295779 : ℕ)^2119*100000000000000^1607 ≤ 42780978812543^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252295779 10000000000 42780978812543 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001380269/10000000000 : ℝ), (219156617/400000000 : ℝ), (5252295779/10000000000 : ℝ)] ![(2996877401289/25000000000000 : ℝ), (9046302313667/20000000000000 : ℝ), (42780978812543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001380269/10000000000 : ℝ)|^2119 ≤ (2996877401289/25000000000000 : ℝ)^1607
        have hw : |(-2001380269/10000000000 : ℝ)|=(2001380269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219156617/400000000 : ℝ)|^2119 ≤ (9046302313667/20000000000000 : ℝ)^1607
        have hw : |(219156617/400000000 : ℝ)|=(219156617/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252295779/10000000000 : ℝ)|^2119 ≤ (42780978812543/100000000000000 : ℝ)^1607
        have hw : |(5252295779/10000000000 : ℝ)|=(5252295779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_13 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5382911227/10000000000 : ℝ)*x 0 + (-1065997493/5000000000 : ℝ)*x 1 + (525229557/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382911227/10000000000 : ℝ)^2119 ≤ (22094677516413/50000000000000 : ℝ)^1607 := by
    have hnat : (5382911227 : ℕ)^2119*50000000000000^1607 ≤ 22094677516413^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382911227 10000000000 22094677516413 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065997493/5000000000 : ℝ)^2119 ≤ (6514834186629/50000000000000 : ℝ)^1607 := by
    have hnat : (1065997493 : ℕ)^2119*50000000000000^1607 ≤ 6514834186629^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065997493 5000000000 6514834186629 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525229557/1000000000 : ℝ)^2119 ≤ (42780976567819/100000000000000 : ℝ)^1607 := by
    have hnat : (525229557 : ℕ)^2119*100000000000000^1607 ≤ 42780976567819^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525229557 1000000000 42780976567819 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382911227/10000000000 : ℝ), (-1065997493/5000000000 : ℝ), (525229557/1000000000 : ℝ)] ![(22094677516413/50000000000000 : ℝ), (6514834186629/50000000000000 : ℝ), (42780976567819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382911227/10000000000 : ℝ)|^2119 ≤ (22094677516413/50000000000000 : ℝ)^1607
        have hw : |(5382911227/10000000000 : ℝ)|=(5382911227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065997493/5000000000 : ℝ)|^2119 ≤ (6514834186629/50000000000000 : ℝ)^1607
        have hw : |(-1065997493/5000000000 : ℝ)|=(1065997493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525229557/1000000000 : ℝ)|^2119 ≤ (42780976567819/100000000000000 : ℝ)^1607
        have hw : |(525229557/1000000000 : ℝ)|=(525229557/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_14 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5382911109/10000000000 : ℝ)*x 0 + (5252295911/10000000000 : ℝ)*x 1 + (-2131994691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382911109/10000000000 : ℝ)^2119 ≤ (5523669219439/12500000000000 : ℝ)^1607 := by
    have hnat : (5382911109 : ℕ)^2119*12500000000000^1607 ≤ 5523669219439^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382911109 10000000000 5523669219439 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5252295911/10000000000 : ℝ)^2119 ≤ (42780980230263/100000000000000 : ℝ)^1607 := by
    have hnat : (5252295911 : ℕ)^2119*100000000000000^1607 ≤ 42780980230263^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252295911 10000000000 42780980230263 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2131994691/10000000000 : ℝ)^2119 ≤ (13029665995957/100000000000000 : ℝ)^1607 := by
    have hnat : (2131994691 : ℕ)^2119*100000000000000^1607 ≤ 13029665995957^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131994691 10000000000 13029665995957 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382911109/10000000000 : ℝ), (5252295911/10000000000 : ℝ), (-2131994691/10000000000 : ℝ)] ![(5523669219439/12500000000000 : ℝ), (42780980230263/100000000000000 : ℝ), (13029665995957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382911109/10000000000 : ℝ)|^2119 ≤ (5523669219439/12500000000000 : ℝ)^1607
        have hw : |(5382911109/10000000000 : ℝ)|=(5382911109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5252295911/10000000000 : ℝ)|^2119 ≤ (42780980230263/100000000000000 : ℝ)^1607
        have hw : |(5252295911/10000000000 : ℝ)|=(5252295911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2131994691/10000000000 : ℝ)|^2119 ≤ (13029665995957/100000000000000 : ℝ)^1607
        have hw : |(-2131994691/10000000000 : ℝ)|=(2131994691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_box_15 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (166679679/400000000 : ℝ)*x 0 + (13861591/31250000 : ℝ)*x 1 + (4435708287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166679679/400000000 : ℝ)^2119 ≤ (15763979112179/50000000000000 : ℝ)^1607 := by
    have hnat : (166679679 : ℕ)^2119*50000000000000^1607 ≤ 15763979112179^1607*400000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166679679 400000000 15763979112179 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13861591/31250000 : ℝ)^2119 ≤ (2139751569753/6250000000000 : ℝ)^1607 := by
    have hnat : (13861591 : ℕ)^2119*6250000000000^1607 ≤ 2139751569753^1607*31250000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13861591 31250000 2139751569753 6250000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4435708287/10000000000 : ℝ)^2119 ≤ (34236016638303/100000000000000 : ℝ)^1607 := by
    have hnat : (4435708287 : ℕ)^2119*100000000000000^1607 ≤ 34236016638303^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435708287 10000000000 34236016638303 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166679679/400000000 : ℝ), (13861591/31250000 : ℝ), (4435708287/10000000000 : ℝ)] ![(15763979112179/50000000000000 : ℝ), (2139751569753/6250000000000 : ℝ), (34236016638303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166679679/400000000 : ℝ)|^2119 ≤ (15763979112179/50000000000000 : ℝ)^1607
        have hw : |(166679679/400000000 : ℝ)|=(166679679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(13861591/31250000 : ℝ)|^2119 ≤ (2139751569753/6250000000000 : ℝ)^1607
        have hw : |(13861591/31250000 : ℝ)|=(13861591/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4435708287/10000000000 : ℝ)|^2119 ≤ (34236016638303/100000000000000 : ℝ)^1607
        have hw : |(4435708287/10000000000 : ℝ)|=(4435708287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(15709/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58819/100000 : ℝ) ∧ (79571/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84099/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7331/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (687/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7331/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (687/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7331/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (687/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7331/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (687/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7331/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (687/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7331/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (687/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (687/6250 : ℝ) ^ (4237/1024 : ℝ) ≤ (2692822000104473/25000000000000000000 : ℝ) := by
    have hpowers : (687/6250 : ℝ)^4237 ≤ (2692822000104473/25000000000000000000 : ℝ)^1024 := by
      have hnat : (687 : ℕ)^4237*25000000000000000000^1024 ≤ 2692822000104473^1024*6250^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        687 6250 2692822000104473 25000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (687/6250 : ℝ)) (X := (2692822000104473/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7331/50000 : ℝ) ^ (4237/1024 : ℝ) ≤ (8869549943958447/25000000000000000000 : ℝ) := by
    have hpowers : (7331/50000 : ℝ)^4237 ≤ (8869549943958447/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7331 : ℕ)^4237*25000000000000000000^1024 ≤ 8869549943958447^1024*50000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7331 50000 8869549943958447 25000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7331/50000 : ℝ)) (X := (8869549943958447/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502692822000104473/12500000000000000000 : ℝ) ≤ (5000260299695623/5000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (12502692822000104473/12500000000000000000 : ℝ)^1024 ≤ (5000260299695623/5000000000000000 : ℝ)^4237 := by
      have hnat : (12502692822000104473 : ℕ)^1024*5000000000000000^4237 ≤ 5000260299695623^4237*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502692822000104473 12500000000000000000 5000260299695623 5000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000260299695623/5000000000000000 : ℝ)) (X := (12502692822000104473/12500000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (625289059298601573/625000000000000000 : ℝ) ≤ (2000223512734489/2000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (625289059298601573/625000000000000000 : ℝ)^1024 ≤ (2000223512734489/2000000000000000 : ℝ)^4237 := by
      have hnat : (625289059298601573 : ℕ)^1024*2000000000000000^4237 ≤ 2000223512734489^4237*625000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625289059298601573 625000000000000000 2000223512734489 2000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000223512734489/2000000000000000 : ℝ)) (X := (625289059298601573/625000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508869549943958447/12500000000000000000 : ℝ) ≤ (2500428631988411/2500000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (12508869549943958447/12500000000000000000 : ℝ)^1024 ≤ (2500428631988411/2500000000000000 : ℝ)^4237 := by
      have hnat : (12508869549943958447 : ℕ)^1024*2500000000000000^4237 ≤ 2500428631988411^4237*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508869549943958447 12500000000000000000 2500428631988411 2500000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500428631988411/2500000000000000 : ℝ)) (X := (12508869549943958447/12500000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2692822000104473/25000000000000000000 : ℝ) ≤ ((9172196734251998501/9175000000000000000 : ℝ)+2*(596964281199/367000000000000 : ℝ)*(687/6250 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (9172196734251998501/9175000000000000000 : ℝ)+2*(596964281199/367000000000000 : ℝ)*(687/6250 : ℝ)=(5000260299695623/5000000000000000 : ℝ) by norm_num, show 1+2*(2692822000104473/25000000000000000000 : ℝ)=(12502692822000104473/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8869549943958447/25000000000000000000 : ℝ)+(2692822000104473/25000000000000000000 : ℝ) ≤ ((9172196734251998501/9175000000000000000 : ℝ)+(596964281199/367000000000000 : ℝ)*((7331/50000 : ℝ)+(687/6250 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (9172196734251998501/9175000000000000000 : ℝ)+(596964281199/367000000000000 : ℝ)*((7331/50000 : ℝ)+(687/6250 : ℝ))=(2000223512734489/2000000000000000 : ℝ) by norm_num, show 1+(8869549943958447/25000000000000000000 : ℝ)+(2692822000104473/25000000000000000000 : ℝ)=(625289059298601573/625000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8869549943958447/25000000000000000000 : ℝ) ≤ ((9172196734251998501/9175000000000000000 : ℝ)+2*(596964281199/367000000000000 : ℝ)*(7331/50000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (9172196734251998501/9175000000000000000 : ℝ)+2*(596964281199/367000000000000 : ℝ)*(7331/50000 : ℝ)=(2500428631988411/2500000000000000 : ℝ) by norm_num, show 1+2*(8869549943958447/25000000000000000000 : ℝ)=(12508869549943958447/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9172196734251998501/9175000000000000000 : ℝ)*(X 1 0+X 2 0)+(596964281199/367000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (9172196734251998501/9175000000000000000 : ℝ)) (alpha := (596964281199/367000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9172196734251998501/9175000000000000000 : ℝ)*(X 0 1+X 2 1)+(596964281199/367000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (9172196734251998501/9175000000000000000 : ℝ)) (alpha := (596964281199/367000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9172196734251998501/9175000000000000000 : ℝ)*(X 0 2+X 1 2)+(596964281199/367000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (687/6250 : ℝ)) (hi := (7331/50000 : ℝ)) (c := (9172196734251998501/9175000000000000000 : ℝ)) (alpha := (596964281199/367000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1928050871/10000000000 : ℝ)*X 0 0+(5392586487/10000000000 : ℝ)*X 0 1+(5392586487/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((264205297/500000000 : ℝ)*X 1 0+(-2076325671/10000000000 : ℝ)*X 1 1+(5392586329/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5284105737/10000000000 : ℝ)*X 2 0+(337036641/625000000 : ℝ)*X 2 1+(-2076326043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4493432671/10000000000 : ℝ)*X 0 0+(2136391113/5000000000 : ℝ)*X 0 1+(4272782257/10000000000 : ℝ)*X 0 2+(4493432671/10000000000 : ℝ)*X 1 0+(2136391113/5000000000 : ℝ)*X 1 1+(4272782257/10000000000 : ℝ)*X 1 2+(4493432671/10000000000 : ℝ)*X 2 0+(2136391113/5000000000 : ℝ)*X 2 1+(4272782257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1137942131/5000000000 : ℝ)*X 0 0+(2631651839/5000000000 : ℝ)*X 0 1+(1052660819/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1343790203/2500000000 : ℝ)*X 1 0+(-2127725331/10000000000 : ℝ)*X 1 1+(5263303993/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((671895151/1250000000 : ℝ)*X 2 0+(5263303661/10000000000 : ℝ)*X 2 1+(-1063862621/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((524127221/1250000000 : ℝ)*X 0 0+(2211466993/5000000000 : ℝ)*X 0 1+(4422933617/10000000000 : ℝ)*X 0 2+(524127221/1250000000 : ℝ)*X 1 0+(2211466993/5000000000 : ℝ)*X 1 1+(4422933617/10000000000 : ℝ)*X 1 2+(524127221/1250000000 : ℝ)*X 2 0+(2211466993/5000000000 : ℝ)*X 2 1+(4422933617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2203024061/10000000000 : ℝ)*X 0 0+(5174616063/10000000000 : ℝ)*X 0 1+(5406628823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637104791/5000000000 : ℝ)*X 1 0+(-517651527/2500000000 : ℝ)*X 1 1+(540662809/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274209753/10000000000 : ℝ)*X 2 0+(5406628171/10000000000 : ℝ)*X 2 1+(-258825721/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2262750951/5000000000 : ℝ)*X 0 0+(425646047/1000000000 : ℝ)*X 0 1+(2128229647/5000000000 : ℝ)*X 0 2+(2262750951/5000000000 : ℝ)*X 1 0+(425646047/1000000000 : ℝ)*X 1 1+(2128229647/5000000000 : ℝ)*X 1 2+(2262750951/5000000000 : ℝ)*X 2 0+(425646047/1000000000 : ℝ)*X 2 1+(2128229647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2001380269/10000000000 : ℝ)*X 0 0+(219156617/400000000 : ℝ)*X 0 1+(5252295779/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5382911227/10000000000 : ℝ)*X 1 0+(-1065997493/5000000000 : ℝ)*X 1 1+(525229557/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5382911109/10000000000 : ℝ)*X 2 0+(5252295911/10000000000 : ℝ)*X 2 1+(-2131994691/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((166679679/400000000 : ℝ)*X 0 0+(13861591/31250000 : ℝ)*X 0 1+(4435708287/10000000000 : ℝ)*X 0 2+(166679679/400000000 : ℝ)*X 1 0+(13861591/31250000 : ℝ)*X 1 1+(4435708287/10000000000 : ℝ)*X 1 2+(166679679/400000000 : ℝ)*X 2 0+(13861591/31250000 : ℝ)*X 2 1+(4435708287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15709/25000 : ℝ) ≤ (-72062254193706242245418340335283/114687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18000489/50000000000000 : ℝ)*(upper1) + (96456483/100000000000000 : ℝ)*(lower2) + (225131/20000000000000 : ℝ)*(lower3) + (31582621/100000000000000 : ℝ)*(upper5) + (1424015522759239/50000000000000 : ℝ)*(major0) + (1424015522759239/50000000000000 : ℝ)*(major1) + (1424015522759239/50000000000000 : ℝ)*(major2) + (6132725201/100000000000000 : ℝ)*(sp2) + (3503917121/100000000000000 : ℝ)*(sp3) + (3845914808342341/100000000000000 : ℝ)*(sp4) + (961479179387779/25000000000000 : ℝ)*(sp5) + (961477646206479/25000000000000 : ℝ)*(sp6) + (935543196974177/50000000000000 : ℝ)*(sp7) + (76368351/4000000000000 : ℝ)*(sp12) + (467772474466369/25000000000000 : ℝ)*(f.failure) + (961479179387779/25000000000000 : ℝ)*(f.sum) + (39092812190511/9175000000000000000000000000 : ℝ)*base65 + (809711147475324261/458750000000000000000000000000000 : ℝ)*base68 + (2003768893255324261/458750000000000000000000000000000 : ℝ)*base70 + (1810510449819675739/458750000000000000000000000000000 : ℝ)*base71 + (23279564377611/9175000000000000000000000000 : ℝ)*base73 + (1230756365700324261/458750000000000000000000000000000 : ℝ)*base76 + (4536194174669074261/458750000000000000000000000000000 : ℝ)*base78 + (858628283416574261/458750000000000000000000000000000 : ℝ)*base80 + (41562346437561/9175000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (13905659/2500000000000000000000 : ℝ)*base89 + (13905659/2500000000000000000000 : ℝ)*base91 + (13905659/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58819/100000 : ℝ) ≤ (33730170812712915144409574112351/57343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8396079/50000000000000 : ℝ)*(lower0) + (48714009/100000000000000 : ℝ)*(upper1) + (169134747/100000000000000 : ℝ)*(upper2) + (10688937/50000000000000 : ℝ)*(upper3) + (728646815454617/25000000000000 : ℝ)*(major0) + (728646815454617/25000000000000 : ℝ)*(major1) + (728646815454617/25000000000000 : ℝ)*(major2) + (3894749305722363/100000000000000 : ℝ)*(sp0) + (1947375871792323/50000000000000 : ℝ)*(sp1) + (1947330362782711/50000000000000 : ℝ)*(sp2) + (191481540102333/10000000000000 : ℝ)*(sp3) + (75384331/20000000000000 : ℝ)*(sp7) + (91018019223/100000000000000 : ℝ)*(sp10) + (1218931141/50000000000000 : ℝ)*(sp12) + (382963155588997/20000000000000 : ℝ)*(f.failure) + (1947375871792323/50000000000000 : ℝ)*(f.sum) + (54162571513741/9175000000000000000000000000 : ℝ)*base65 + (1842488333142270883/229375000000000000000000000000000 : ℝ)*base68 + (905317216405395883/229375000000000000000000000000000 : ℝ)*base70 + (68586875969145883/229375000000000000000000000000000 : ℝ)*base72 + (5623981197317/4587500000000000000000000000 : ℝ)*base74 + (2156440418608520883/229375000000000000000000000000000 : ℝ)*base76 + (200765733823979117/229375000000000000000000000000000 : ℝ)*base77 + (657620239378520883/229375000000000000000000000000000 : ℝ)*base80 + (27041042117059/9175000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1558233/2000000000000000000000 : ℝ)*base90 + (1558233/2000000000000000000000 : ℝ)*base92 + (1558233/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79571/100000 : ℝ) ≤ (91260998011793719525465458281949/114687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (17261001/100000000000000 : ℝ)*(upper0) + (90121423/50000000000000 : ℝ)*(upper1) + (44401343/25000000000000 : ℝ)*(upper4) + (807256442280983/25000000000000 : ℝ)*(major0) + (807256442280983/25000000000000 : ℝ)*(major1) + (807256442280983/25000000000000 : ℝ)*(major2) + (34179858859/100000000000000 : ℝ)*(sp1) + (6958768303/5000000000000 : ℝ)*(sp2) + (12840735559/12500000000000 : ℝ)*(sp3) + (12815960527/100000000000000 : ℝ)*(sp4) + (134691238942477/3125000000000 : ℝ)*(sp8) + (1077524570565233/25000000000000 : ℝ)*(sp9) + (430999328675373/10000000000000 : ℝ)*(sp10) + (2121291809495387/100000000000000 : ℝ)*(sp11) + (2121394535379859/100000000000000 : ℝ)*(f.failure) + (431013246211979/10000000000000 : ℝ)*(f.sum) + (34692209211917/4587500000000000000000000000 : ℝ)*base65 + (314547065264731483/229375000000000000000000000000000 : ℝ)*base67 + (634481168844106483/229375000000000000000000000000000 : ℝ)*base69 + (185366840604018517/229375000000000000000000000000000 : ℝ)*base72 + (66532847166241/9175000000000000000000000000 : ℝ)*base74 + (2288993615229643517/229375000000000000000000000000000 : ℝ)*base76 + (601462730317768517/229375000000000000000000000000000 : ℝ)*base78 + (2912672768162768517/229375000000000000000000000000000 : ℝ)*base80 + (1126808598851/573437500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (60769951/10000000000000000000000 : ℝ)*base90 + (60769951/10000000000000000000000 : ℝ)*base92 + (60769951/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-84099/100000 : ℝ) ≤ (-12056008298941702152025850903967/14335937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (10187013/6250000000000 : ℝ)*(lower0) + (2070833/6250000000000 : ℝ)*(lower1) + (47816579/50000000000000 : ℝ)*(lower2) + (408095634312353/12500000000000 : ℝ)*(major0) + (408095634312353/12500000000000 : ℝ)*(major1) + (408095634312353/12500000000000 : ℝ)*(major2) + (25787861/160000000000 : ℝ)*(sp0) + (31927446411/10000000000000 : ℝ)*(sp5) + (32177212741/25000000000000 : ℝ)*(sp6) + (53179608443/100000000000000 : ℝ)*(sp7) + (4412671742609247/100000000000000 : ℝ)*(sp12) + (2206184292779131/50000000000000 : ℝ)*(sp13) + (275784946948213/6250000000000 : ℝ)*(sp14) + (13405132780757/625000000000 : ℝ)*(sp15) + (2144874424529563/100000000000000 : ℝ)*(f.failure) + (1103171965005593/25000000000000 : ℝ)*(f.sum) + (25045742308719/4587500000000000000000000000 : ℝ)*base65 + (1041967348335457853/114687500000000000000000000000000 : ℝ)*base67 + (840103011136395353/114687500000000000000000000000000 : ℝ)*base69 + (652826127088582853/114687500000000000000000000000000 : ℝ)*base71 + (128114990486547/2293750000000000000000000000 : ℝ)*base73 + (632688664955479647/114687500000000000000000000000000 : ℝ)*base76 + (1171476124985457853/114687500000000000000000000000000 : ℝ)*base77 + (5329477529456082853/114687500000000000000000000000000 : ℝ)*base79 + (50808042362137/9175000000000000000000000000 : ℝ)*base82 + (74993607/10000000000000000000000 : ℝ)*base90 + (74993607/10000000000000000000000 : ℝ)*base92 + (74993607/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1278_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7331/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (687/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58819/100000 : ℝ) else (79571/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84099/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1278_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1278_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10977/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58819/100000 : ℝ) else (79571/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84099/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1278_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1278_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1278_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10977/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58819/100000 : ℝ) else (79571/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84099/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1278_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
