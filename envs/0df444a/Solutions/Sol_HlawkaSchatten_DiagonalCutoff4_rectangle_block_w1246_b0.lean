-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1246_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:21:33.457869+00:00
-- url     : https://prove2.me/submissions/7df1def7-729b-4bd0-9af3-c74bfda916cf

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
theorem support_rectangle_w1246_s0_0 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-464831621/2500000000 : ℝ)*x 0 + (6030604221/10000000000 : ℝ)*x 1 + (4793482851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464831621/2500000000 : ℝ)^8439 ≤ (10844766662829/100000000000000 : ℝ)^6391 := by
    have hnat : (464831621 : ℕ)^8439*100000000000000^6391 ≤ 10844766662829^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464831621 2500000000 10844766662829 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6030604221/10000000000 : ℝ)^8439 ≤ (51283459615251/100000000000000 : ℝ)^6391 := by
    have hnat : (6030604221 : ℕ)^8439*100000000000000^6391 ≤ 51283459615251^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6030604221 10000000000 51283459615251 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4793482851/10000000000 : ℝ)^8439 ≤ (302974189677/800000000000 : ℝ)^6391 := by
    have hnat : (4793482851 : ℕ)^8439*800000000000^6391 ≤ 302974189677^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793482851 10000000000 302974189677 800000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464831621/2500000000 : ℝ), (6030604221/10000000000 : ℝ), (4793482851/10000000000 : ℝ)] ![(10844766662829/100000000000000 : ℝ), (51283459615251/100000000000000 : ℝ), (302974189677/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464831621/2500000000 : ℝ)|^8439 ≤ (10844766662829/100000000000000 : ℝ)^6391
        have hw : |(-464831621/2500000000 : ℝ)|=(464831621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6030604221/10000000000 : ℝ)|^8439 ≤ (51283459615251/100000000000000 : ℝ)^6391
        have hw : |(6030604221/10000000000 : ℝ)|=(6030604221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4793482851/10000000000 : ℝ)|^8439 ≤ (302974189677/800000000000 : ℝ)^6391
        have hw : |(4793482851/10000000000 : ℝ)|=(4793482851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s0_1 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (110218683/200000000 : ℝ)*x 0 + (-1283225569/5000000000 : ℝ)*x 1 + (2396741397/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (110218683/200000000 : ℝ)^8439 ≤ (45530317622501/100000000000000 : ℝ)^6391 := by
    have hnat : (110218683 : ℕ)^8439*100000000000000^6391 ≤ 45530317622501^6391*200000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110218683 200000000 45530317622501 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283225569/5000000000 : ℝ)^8439 ≤ (4149477313939/25000000000000 : ℝ)^6391 := by
    have hnat : (1283225569 : ℕ)^8439*25000000000000^6391 ≤ 4149477313939^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283225569 5000000000 4149477313939 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2396741397/5000000000 : ℝ)^8439 ≤ (1514870924599/4000000000000 : ℝ)^6391 := by
    have hnat : (2396741397 : ℕ)^8439*4000000000000^6391 ≤ 1514870924599^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396741397 5000000000 1514870924599 4000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(110218683/200000000 : ℝ), (-1283225569/5000000000 : ℝ), (2396741397/5000000000 : ℝ)] ![(45530317622501/100000000000000 : ℝ), (4149477313939/25000000000000 : ℝ), (1514870924599/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(110218683/200000000 : ℝ)|^8439 ≤ (45530317622501/100000000000000 : ℝ)^6391
        have hw : |(110218683/200000000 : ℝ)|=(110218683/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1283225569/5000000000 : ℝ)|^8439 ≤ (4149477313939/25000000000000 : ℝ)^6391
        have hw : |(-1283225569/5000000000 : ℝ)|=(1283225569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2396741397/5000000000 : ℝ)|^8439 ≤ (1514870924599/4000000000000 : ℝ)^6391
        have hw : |(2396741397/5000000000 : ℝ)|=(2396741397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s0_2 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5510934067/10000000000 : ℝ)*x 0 + (4793482881/10000000000 : ℝ)*x 1 + (-2566451137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5510934067/10000000000 : ℝ)^8439 ≤ (45530316717027/100000000000000 : ℝ)^6391 := by
    have hnat : (5510934067 : ℕ)^8439*100000000000000^6391 ≤ 45530316717027^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5510934067 10000000000 45530316717027 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4793482881/10000000000 : ℝ)^8439 ≤ (37871774022599/100000000000000 : ℝ)^6391 := by
    have hnat : (4793482881 : ℕ)^8439*100000000000000^6391 ≤ 37871774022599^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4793482881 10000000000 37871774022599 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2566451137/10000000000 : ℝ)^8439 ≤ (1037369327951/6250000000000 : ℝ)^6391 := by
    have hnat : (2566451137 : ℕ)^8439*6250000000000^6391 ≤ 1037369327951^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2566451137 10000000000 1037369327951 6250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5510934067/10000000000 : ℝ), (4793482881/10000000000 : ℝ), (-2566451137/10000000000 : ℝ)] ![(45530316717027/100000000000000 : ℝ), (37871774022599/100000000000000 : ℝ), (1037369327951/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5510934067/10000000000 : ℝ)|^8439 ≤ (45530316717027/100000000000000 : ℝ)^6391
        have hw : |(5510934067/10000000000 : ℝ)|=(5510934067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4793482881/10000000000 : ℝ)|^8439 ≤ (37871774022599/100000000000000 : ℝ)^6391
        have hw : |(4793482881/10000000000 : ℝ)|=(4793482881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2566451137/10000000000 : ℝ)|^8439 ≤ (1037369327951/6250000000000 : ℝ)^6391
        have hw : |(-2566451137/10000000000 : ℝ)|=(2566451137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s0_3 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (209635377/500000000 : ℝ)*x 0 + (3116741467/10000000000 : ℝ)*x 1 + (225130709/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209635377/500000000 : ℝ)^8439 ≤ (31733846381277/100000000000000 : ℝ)^6391 := by
    have hnat : (209635377 : ℕ)^8439*100000000000000^6391 ≤ 31733846381277^6391*500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209635377 500000000 31733846381277 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116741467/10000000000 : ℝ)^8439 ≤ (5362865211023/25000000000000 : ℝ)^6391 := by
    have hnat : (3116741467 : ℕ)^8439*25000000000000^6391 ≤ 5362865211023^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116741467 10000000000 5362865211023 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225130709/400000000 : ℝ)^8439 ≤ (23407346378087/50000000000000 : ℝ)^6391 := by
    have hnat : (225130709 : ℕ)^8439*50000000000000^6391 ≤ 23407346378087^6391*400000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225130709 400000000 23407346378087 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209635377/500000000 : ℝ), (3116741467/10000000000 : ℝ), (225130709/400000000 : ℝ)] ![(31733846381277/100000000000000 : ℝ), (5362865211023/25000000000000 : ℝ), (23407346378087/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209635377/500000000 : ℝ)|^8439 ≤ (31733846381277/100000000000000 : ℝ)^6391
        have hw : |(209635377/500000000 : ℝ)|=(209635377/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116741467/10000000000 : ℝ)|^8439 ≤ (5362865211023/25000000000000 : ℝ)^6391
        have hw : |(3116741467/10000000000 : ℝ)|=(3116741467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225130709/400000000 : ℝ)|^8439 ≤ (23407346378087/50000000000000 : ℝ)^6391
        have hw : |(225130709/400000000 : ℝ)|=(225130709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s0_4 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-932086317/5000000000 : ℝ)*x 0 + (482533881/1000000000 : ℝ)*x 1 + (5997622167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (932086317/5000000000 : ℝ)^8439 ≤ (136026323061/1250000000000 : ℝ)^6391 := by
    have hnat : (932086317 : ℕ)^8439*1250000000000^6391 ≤ 136026323061^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932086317 5000000000 136026323061 1250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482533881/1000000000 : ℝ)^8439 ≤ (19102231500013/50000000000000 : ℝ)^6391 := by
    have hnat : (482533881 : ℕ)^8439*50000000000000^6391 ≤ 19102231500013^6391*1000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482533881 1000000000 19102231500013 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5997622167/10000000000 : ℝ)^8439 ≤ (50913431138571/100000000000000 : ℝ)^6391 := by
    have hnat : (5997622167 : ℕ)^8439*100000000000000^6391 ≤ 50913431138571^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5997622167 10000000000 50913431138571 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-932086317/5000000000 : ℝ), (482533881/1000000000 : ℝ), (5997622167/10000000000 : ℝ)] ![(136026323061/1250000000000 : ℝ), (19102231500013/50000000000000 : ℝ), (50913431138571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-932086317/5000000000 : ℝ)|^8439 ≤ (136026323061/1250000000000 : ℝ)^6391
        have hw : |(-932086317/5000000000 : ℝ)|=(932086317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482533881/1000000000 : ℝ)|^8439 ≤ (19102231500013/50000000000000 : ℝ)^6391
        have hw : |(482533881/1000000000 : ℝ)|=(482533881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5997622167/10000000000 : ℝ)|^8439 ≤ (50913431138571/100000000000000 : ℝ)^6391
        have hw : |(5997622167/10000000000 : ℝ)|=(5997622167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s0_5 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174314023/10000000000 : ℝ)*x 0 + (-21286087/156250000 : ℝ)*x 1 + (2998812241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174314023/10000000000 : ℝ)^8439 ≤ (41894472320391/100000000000000 : ℝ)^6391 := by
    have hnat : (5174314023 : ℕ)^8439*100000000000000^6391 ≤ 41894472320391^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174314023 10000000000 41894472320391 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21286087/156250000 : ℝ)^8439 ≤ (359603528833/5000000000000 : ℝ)^6391 := by
    have hnat : (21286087 : ℕ)^8439*5000000000000^6391 ≤ 359603528833^6391*156250000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21286087 156250000 359603528833 5000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2998812241/5000000000 : ℝ)^8439 ≤ (636418213599/1250000000000 : ℝ)^6391 := by
    have hnat : (2998812241 : ℕ)^8439*1250000000000^6391 ≤ 636418213599^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2998812241 5000000000 636418213599 1250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174314023/10000000000 : ℝ), (-21286087/156250000 : ℝ), (2998812241/5000000000 : ℝ)] ![(41894472320391/100000000000000 : ℝ), (359603528833/5000000000000 : ℝ), (636418213599/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174314023/10000000000 : ℝ)|^8439 ≤ (41894472320391/100000000000000 : ℝ)^6391
        have hw : |(5174314023/10000000000 : ℝ)|=(5174314023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21286087/156250000 : ℝ)|^8439 ≤ (359603528833/5000000000000 : ℝ)^6391
        have hw : |(-21286087/156250000 : ℝ)|=(21286087/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2998812241/5000000000 : ℝ)|^8439 ≤ (636418213599/1250000000000 : ℝ)^6391
        have hw : |(2998812241/5000000000 : ℝ)|=(2998812241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s0_6 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5174314963/10000000000 : ℝ)*x 0 + (5997622611/10000000000 : ℝ)*x 1 + (-272462227/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174314963/10000000000 : ℝ)^8439 ≤ (41894482370111/100000000000000 : ℝ)^6391 := by
    have hnat : (5174314963 : ℕ)^8439*100000000000000^6391 ≤ 41894482370111^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174314963 10000000000 41894482370111 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5997622611/10000000000 : ℝ)^8439 ≤ (25456718057733/50000000000000 : ℝ)^6391 := by
    have hnat : (5997622611 : ℕ)^8439*50000000000000^6391 ≤ 25456718057733^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5997622611 10000000000 25456718057733 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272462227/2000000000 : ℝ)^8439 ≤ (143841630007/2000000000000 : ℝ)^6391 := by
    have hnat : (272462227 : ℕ)^8439*2000000000000^6391 ≤ 143841630007^6391*2000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272462227 2000000000 143841630007 2000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174314963/10000000000 : ℝ), (5997622611/10000000000 : ℝ), (-272462227/2000000000 : ℝ)] ![(41894482370111/100000000000000 : ℝ), (25456718057733/50000000000000 : ℝ), (143841630007/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174314963/10000000000 : ℝ)|^8439 ≤ (41894482370111/100000000000000 : ℝ)^6391
        have hw : |(5174314963/10000000000 : ℝ)|=(5174314963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5997622611/10000000000 : ℝ)|^8439 ≤ (25456718057733/50000000000000 : ℝ)^6391
        have hw : |(5997622611/10000000000 : ℝ)|=(5997622611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272462227/2000000000 : ℝ)|^8439 ≤ (143841630007/2000000000000 : ℝ)^6391
        have hw : |(-272462227/2000000000 : ℝ)|=(272462227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s0_7 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4202547187/10000000000 : ℝ)*x 0 + (5563601107/10000000000 : ℝ)*x 1 + (318369367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202547187/10000000000 : ℝ)^8439 ≤ (6366444651179/20000000000000 : ℝ)^6391 := by
    have hnat : (4202547187 : ℕ)^8439*20000000000000^6391 ≤ 6366444651179^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202547187 10000000000 6366444651179 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5563601107/10000000000 : ℝ)^8439 ≤ (46105756134303/100000000000000 : ℝ)^6391 := by
    have hnat : (5563601107 : ℕ)^8439*100000000000000^6391 ≤ 46105756134303^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5563601107 10000000000 46105756134303 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318369367/1000000000 : ℝ)^8439 ≤ (4412404119161/20000000000000 : ℝ)^6391 := by
    have hnat : (318369367 : ℕ)^8439*20000000000000^6391 ≤ 4412404119161^6391*1000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318369367 1000000000 4412404119161 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202547187/10000000000 : ℝ), (5563601107/10000000000 : ℝ), (318369367/1000000000 : ℝ)] ![(6366444651179/20000000000000 : ℝ), (46105756134303/100000000000000 : ℝ), (4412404119161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202547187/10000000000 : ℝ)|^8439 ≤ (6366444651179/20000000000000 : ℝ)^6391
        have hw : |(4202547187/10000000000 : ℝ)|=(4202547187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5563601107/10000000000 : ℝ)|^8439 ≤ (46105756134303/100000000000000 : ℝ)^6391
        have hw : |(5563601107/10000000000 : ℝ)|=(5563601107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(318369367/1000000000 : ℝ)|^8439 ≤ (4412404119161/20000000000000 : ℝ)^6391
        have hw : |(318369367/1000000000 : ℝ)|=(318369367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1246_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (417/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27421/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4219/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4219 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4219*1^1024 ≤ 0^1024*1^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4219/1024 : ℝ) ≤ (2293192594797537839/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4219 ≤ (2293192594797537839/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4219*100000000000000000000^1024 ≤ 2293192594797537839^1024*5^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2293192594797537839 100000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2293192594797537839/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4219 := by
      have hnat : (1 : ℕ)^1024*1^4219 ≤ 1^4219*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102293192594797537839/100000000000000000000 : ℝ) ≤ (201103630755339/200000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (102293192594797537839/100000000000000000000 : ℝ)^1024 ≤ (201103630755339/200000000000000 : ℝ)^4219 := by
      have hnat : (102293192594797537839 : ℕ)^1024*200000000000000^4219 ≤ 201103630755339^4219*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102293192594797537839 100000000000000000000 201103630755339 200000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (201103630755339/200000000000000 : ℝ)) (X := (102293192594797537839/100000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52293192594797537839/50000000000000000000 : ℝ) ≤ (101103630755339/100000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (52293192594797537839/50000000000000000000 : ℝ)^1024 ≤ (101103630755339/100000000000000 : ℝ)^4219 := by
      have hnat : (52293192594797537839 : ℕ)^1024*100000000000000^4219 ≤ 101103630755339^4219*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52293192594797537839 50000000000000000000 101103630755339 100000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (101103630755339/100000000000000 : ℝ)) (X := (52293192594797537839/50000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1103630755339/80000000000000 : ℝ)*(0 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1103630755339/80000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2293192594797537839/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1103630755339/80000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4219/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1103630755339/80000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(201103630755339/200000000000000 : ℝ) by norm_num, show 1+(2293192594797537839/100000000000000000000 : ℝ)+(0 : ℝ)=(102293192594797537839/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2293192594797537839/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1103630755339/80000000000000 : ℝ)*(2/5 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1103630755339/80000000000000 : ℝ)*(2/5 : ℝ)=(101103630755339/100000000000000 : ℝ) by norm_num, show 1+2*(2293192594797537839/100000000000000000000 : ℝ)=(52293192594797537839/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1103630755339/80000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1103630755339/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1103630755339/80000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1103630755339/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1103630755339/80000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1103630755339/80000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-464831621/2500000000 : ℝ)*X 0 0+(6030604221/10000000000 : ℝ)*X 0 1+(4793482851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((110218683/200000000 : ℝ)*X 1 0+(-1283225569/5000000000 : ℝ)*X 1 1+(2396741397/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5510934067/10000000000 : ℝ)*X 2 0+(4793482881/10000000000 : ℝ)*X 2 1+(-2566451137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((209635377/500000000 : ℝ)*X 0 0+(3116741467/10000000000 : ℝ)*X 0 1+(225130709/400000000 : ℝ)*X 0 2+(209635377/500000000 : ℝ)*X 1 0+(3116741467/10000000000 : ℝ)*X 1 1+(225130709/400000000 : ℝ)*X 1 2+(209635377/500000000 : ℝ)*X 2 0+(3116741467/10000000000 : ℝ)*X 2 1+(225130709/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-932086317/5000000000 : ℝ)*X 0 0+(482533881/1000000000 : ℝ)*X 0 1+(5997622167/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174314023/10000000000 : ℝ)*X 1 0+(-21286087/156250000 : ℝ)*X 1 1+(2998812241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174314963/10000000000 : ℝ)*X 2 0+(5997622611/10000000000 : ℝ)*X 2 1+(-272462227/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4202547187/10000000000 : ℝ)*X 0 0+(5563601107/10000000000 : ℝ)*X 0 1+(318369367/1000000000 : ℝ)*X 0 2+(4202547187/10000000000 : ℝ)*X 1 0+(5563601107/10000000000 : ℝ)*X 1 1+(318369367/1000000000 : ℝ)*X 1 2+(4202547187/10000000000 : ℝ)*X 2 0+(5563601107/10000000000 : ℝ)*X 2 1+(318369367/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (73163383443116999049/15625000000000000000000000 : ℝ) := by norm_num
    linear_combination (59810057/100000000000000 : ℝ)*(base1) + (1143105739/100000000000000 : ℝ)*(base19) + (131960621/12500000000000 : ℝ)*(base23) + (75246489/100000000000000 : ℝ)*(base24) + (254737793/100000000000000 : ℝ)*(upper3) + (18851595337229/3125000000000 : ℝ)*(major0) + (18851595337229/3125000000000 : ℝ)*(major1) + (18851595337229/3125000000000 : ℝ)*(major2) + (202083000159543/25000000000000 : ℝ)*(sp0) + (808333348463959/100000000000000 : ℝ)*(sp1) + (808333360638241/100000000000000 : ℝ)*(sp2) + (49770678174419/12500000000000 : ℝ)*(sp3) + (2550741583/100000000000000 : ℝ)*(sp4) + (1968725659/100000000000000 : ℝ)*(sp7) + (99541863482767/25000000000000 : ℝ)*(f.failure) + (404167245784849/50000000000000 : ℝ)*(f.sum) + (25097181891/7812500000000000000000000 : ℝ)*base65 + (779990680881/250000000000000000000000000 : ℝ)*base67 + (566959349881/250000000000000000000000000 : ℝ)*base69 + (783240924881/250000000000000000000000000 : ℝ)*base71 + (13991981133/3906250000000000000000000 : ℝ)*base73 + (1874918671631/250000000000000000000000000 : ℝ)*base75 + (1410101850631/250000000000000000000000000 : ℝ)*base77 + (1285042661131/250000000000000000000000000 : ℝ)*base79 + (50138438253/62500000000000000000000000 : ℝ)*base81 + (9407943/2500000000000000000000 : ℝ)*base90 + (9407943/2500000000000000000000 : ℝ)*base92 + (9407943/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13967845649867170191501/4000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68149783/50000000000000 : ℝ)*(base1) + (830985849/100000000000000 : ℝ)*(base19) + (14945099/1562500000000 : ℝ)*(base23) + (48692857/25000000000000 : ℝ)*(upper3) + (636610321284049/100000000000000 : ℝ)*(major0) + (636610321284049/100000000000000 : ℝ)*(major1) + (636610321284049/100000000000000 : ℝ)*(major2) + (2105653603/100000000000000 : ℝ)*(sp1) + (826353193/50000000000000 : ℝ)*(sp2) + (10227983/3125000000000 : ℝ)*(sp3) + (853034886680567/100000000000000 : ℝ)*(sp4) + (853031813741549/100000000000000 : ℝ)*(sp5) + (853032141188279/100000000000000 : ℝ)*(sp6) + (420185312193357/100000000000000 : ℝ)*(sp7) + (420185775788379/100000000000000 : ℝ)*(f.failure) + (853034750381001/100000000000000 : ℝ)*(f.sum) + (6887243796389/4000000000000000000000000000 : ℝ)*base66 + (28090038919611/8000000000000000000000000000 : ℝ)*base67 + (56640350455611/8000000000000000000000000000 : ℝ)*base69 + (4502230320389/8000000000000000000000000000 : ℝ)*base72 + (289725867611/4000000000000000000000000000 : ℝ)*base73 + (34878104767611/8000000000000000000000000000 : ℝ)*base75 + (27065077983611/8000000000000000000000000000 : ℝ)*base77 + (3041644799611/8000000000000000000000000000 : ℝ)*base79 + (6662801315611/4000000000000000000000000000 : ℝ)*base81 + (39547891/10000000000000000000000 : ℝ)*base90 + (39547891/10000000000000000000000 : ℝ)*base92 + (39547891/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1246_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (417/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27421/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1246_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1246_s1_0 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1028224067/5000000000 : ℝ)*x 0 + (5674598399/10000000000 : ℝ)*x 1 + (2511654253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1028224067/5000000000 : ℝ)^8439 ≤ (1548516811623/12500000000000 : ℝ)^6391 := by
    have hnat : (1028224067 : ℕ)^8439*12500000000000^6391 ≤ 1548516811623^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028224067 5000000000 1548516811623 12500000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5674598399/10000000000 : ℝ)^8439 ≤ (47324222551751/100000000000000 : ℝ)^6391 := by
    have hnat : (5674598399 : ℕ)^8439*100000000000000^6391 ≤ 47324222551751^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674598399 10000000000 47324222551751 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2511654253/5000000000 : ℝ)^8439 ≤ (20143821472277/50000000000000 : ℝ)^6391 := by
    have hnat : (2511654253 : ℕ)^8439*50000000000000^6391 ≤ 20143821472277^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2511654253 5000000000 20143821472277 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1028224067/5000000000 : ℝ), (5674598399/10000000000 : ℝ), (2511654253/5000000000 : ℝ)] ![(1548516811623/12500000000000 : ℝ), (47324222551751/100000000000000 : ℝ), (20143821472277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1028224067/5000000000 : ℝ)|^8439 ≤ (1548516811623/12500000000000 : ℝ)^6391
        have hw : |(-1028224067/5000000000 : ℝ)|=(1028224067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5674598399/10000000000 : ℝ)|^8439 ≤ (47324222551751/100000000000000 : ℝ)^6391
        have hw : |(5674598399/10000000000 : ℝ)|=(5674598399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2511654253/5000000000 : ℝ)|^8439 ≤ (20143821472277/50000000000000 : ℝ)^6391
        have hw : |(2511654253/5000000000 : ℝ)|=(2511654253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s1_1 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2706719991/5000000000 : ℝ)*x 0 + (-2406116693/10000000000 : ℝ)*x 1 + (1255827157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706719991/5000000000 : ℝ)^8439 ≤ (8893949932851/20000000000000 : ℝ)^6391 := by
    have hnat : (2706719991 : ℕ)^8439*20000000000000^6391 ≤ 8893949932851^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706719991 5000000000 8893949932851 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406116693/10000000000 : ℝ)^8439 ≤ (7621303039933/50000000000000 : ℝ)^6391 := by
    have hnat : (2406116693 : ℕ)^8439*50000000000000^6391 ≤ 7621303039933^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406116693 10000000000 7621303039933 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255827157/2500000000 : ℝ)^8439 ≤ (20143822118279/50000000000000 : ℝ)^6391 := by
    have hnat : (1255827157 : ℕ)^8439*50000000000000^6391 ≤ 20143822118279^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255827157 2500000000 20143822118279 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706719991/5000000000 : ℝ), (-2406116693/10000000000 : ℝ), (1255827157/2500000000 : ℝ)] ![(8893949932851/20000000000000 : ℝ), (7621303039933/50000000000000 : ℝ), (20143822118279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706719991/5000000000 : ℝ)|^8439 ≤ (8893949932851/20000000000000 : ℝ)^6391
        have hw : |(2706719991/5000000000 : ℝ)|=(2706719991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2406116693/10000000000 : ℝ)|^8439 ≤ (7621303039933/50000000000000 : ℝ)^6391
        have hw : |(-2406116693/10000000000 : ℝ)|=(2406116693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255827157/2500000000 : ℝ)|^8439 ≤ (20143822118279/50000000000000 : ℝ)^6391
        have hw : |(1255827157/2500000000 : ℝ)|=(1255827157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s1_2 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1353360023/2500000000 : ℝ)*x 0 + (1255827139/2500000000 : ℝ)*x 1 + (-1203058321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353360023/2500000000 : ℝ)^8439 ≤ (11117437714359/25000000000000 : ℝ)^6391 := by
    have hnat : (1353360023 : ℕ)^8439*25000000000000^6391 ≤ 11117437714359^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353360023 2500000000 11117437714359 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255827139/2500000000 : ℝ)^8439 ≤ (2517977717129/6250000000000 : ℝ)^6391 := by
    have hnat : (1255827139 : ℕ)^8439*6250000000000^6391 ≤ 2517977717129^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255827139 2500000000 2517977717129 6250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1203058321/5000000000 : ℝ)^8439 ≤ (3810651413313/25000000000000 : ℝ)^6391 := by
    have hnat : (1203058321 : ℕ)^8439*25000000000000^6391 ≤ 3810651413313^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203058321 5000000000 3810651413313 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353360023/2500000000 : ℝ), (1255827139/2500000000 : ℝ), (-1203058321/5000000000 : ℝ)] ![(11117437714359/25000000000000 : ℝ), (2517977717129/6250000000000 : ℝ), (3810651413313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353360023/2500000000 : ℝ)|^8439 ≤ (11117437714359/25000000000000 : ℝ)^6391
        have hw : |(1353360023/2500000000 : ℝ)|=(1353360023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255827139/2500000000 : ℝ)|^8439 ≤ (2517977717129/6250000000000 : ℝ)^6391
        have hw : |(1255827139/2500000000 : ℝ)|=(1255827139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1203058321/5000000000 : ℝ)|^8439 ≤ (3810651413313/25000000000000 : ℝ)^6391
        have hw : |(-1203058321/5000000000 : ℝ)|=(1203058321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s1_3 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (134640909/312500000 : ℝ)*x 0 + (3696176113/10000000000 : ℝ)*x 1 + (2509192229/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134640909/312500000 : ℝ)^8439 ≤ (1315851453019/4000000000000 : ℝ)^6391 := by
    have hnat : (134640909 : ℕ)^8439*4000000000000^6391 ≤ 1315851453019^6391*312500000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134640909 312500000 1315851453019 4000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3696176113/10000000000 : ℝ)^8439 ≤ (13434104587783/50000000000000 : ℝ)^6391 := by
    have hnat : (3696176113 : ℕ)^8439*50000000000000^6391 ≤ 13434104587783^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3696176113 10000000000 13434104587783 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2509192229/5000000000 : ℝ)^8439 ≤ (40235504481481/100000000000000 : ℝ)^6391 := by
    have hnat : (2509192229 : ℕ)^8439*100000000000000^6391 ≤ 40235504481481^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509192229 5000000000 40235504481481 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134640909/312500000 : ℝ), (3696176113/10000000000 : ℝ), (2509192229/5000000000 : ℝ)] ![(1315851453019/4000000000000 : ℝ), (13434104587783/50000000000000 : ℝ), (40235504481481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134640909/312500000 : ℝ)|^8439 ≤ (1315851453019/4000000000000 : ℝ)^6391
        have hw : |(134640909/312500000 : ℝ)|=(134640909/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3696176113/10000000000 : ℝ)|^8439 ≤ (13434104587783/50000000000000 : ℝ)^6391
        have hw : |(3696176113/10000000000 : ℝ)|=(3696176113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2509192229/5000000000 : ℝ)|^8439 ≤ (40235504481481/100000000000000 : ℝ)^6391
        have hw : |(2509192229/5000000000 : ℝ)|=(2509192229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s1_4 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2057119593/10000000000 : ℝ)*x 0 + (5031850251/10000000000 : ℝ)*x 1 + (5665894493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2057119593/10000000000 : ℝ)^8439 ≤ (1549184482681/12500000000000 : ℝ)^6391 := by
    have hnat : (2057119593 : ℕ)^8439*12500000000000^6391 ≤ 1549184482681^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2057119593 10000000000 1549184482681 12500000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5031850251/10000000000 : ℝ)^8439 ≤ (5047265796473/12500000000000 : ℝ)^6391 := by
    have hnat : (5031850251 : ℕ)^8439*12500000000000^6391 ≤ 5047265796473^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031850251 10000000000 5047265796473 12500000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5665894493/10000000000 : ℝ)^8439 ≤ (2951774859283/6250000000000 : ℝ)^6391 := by
    have hnat : (5665894493 : ℕ)^8439*6250000000000^6391 ≤ 2951774859283^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665894493 10000000000 2951774859283 6250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2057119593/10000000000 : ℝ), (5031850251/10000000000 : ℝ), (5665894493/10000000000 : ℝ)] ![(1549184482681/12500000000000 : ℝ), (5047265796473/12500000000000 : ℝ), (2951774859283/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2057119593/10000000000 : ℝ)|^8439 ≤ (1549184482681/12500000000000 : ℝ)^6391
        have hw : |(-2057119593/10000000000 : ℝ)|=(2057119593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5031850251/10000000000 : ℝ)|^8439 ≤ (5047265796473/12500000000000 : ℝ)^6391
        have hw : |(5031850251/10000000000 : ℝ)|=(5031850251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5665894493/10000000000 : ℝ)|^8439 ≤ (2951774859283/6250000000000 : ℝ)^6391
        have hw : |(5665894493/10000000000 : ℝ)|=(5665894493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s1_5 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5245616719/10000000000 : ℝ)*x 0 + (-881765329/5000000000 : ℝ)*x 1 + (5665894703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245616719/10000000000 : ℝ)^8439 ≤ (42658461005053/100000000000000 : ℝ)^6391 := by
    have hnat : (5245616719 : ℕ)^8439*100000000000000^6391 ≤ 42658461005053^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245616719 10000000000 42658461005053 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881765329/5000000000 : ℝ)^8439 ≤ (5056569463617/50000000000000 : ℝ)^6391 := by
    have hnat : (881765329 : ℕ)^8439*50000000000000^6391 ≤ 5056569463617^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881765329 5000000000 5056569463617 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5665894703/10000000000 : ℝ)^8439 ≤ (23614200029967/50000000000000 : ℝ)^6391 := by
    have hnat : (5665894703 : ℕ)^8439*50000000000000^6391 ≤ 23614200029967^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665894703 10000000000 23614200029967 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245616719/10000000000 : ℝ), (-881765329/5000000000 : ℝ), (5665894703/10000000000 : ℝ)] ![(42658461005053/100000000000000 : ℝ), (5056569463617/50000000000000 : ℝ), (23614200029967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245616719/10000000000 : ℝ)|^8439 ≤ (42658461005053/100000000000000 : ℝ)^6391
        have hw : |(5245616719/10000000000 : ℝ)|=(5245616719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-881765329/5000000000 : ℝ)|^8439 ≤ (5056569463617/50000000000000 : ℝ)^6391
        have hw : |(-881765329/5000000000 : ℝ)|=(881765329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5665894703/10000000000 : ℝ)|^8439 ≤ (23614200029967/50000000000000 : ℝ)^6391
        have hw : |(5665894703/10000000000 : ℝ)|=(5665894703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s1_6 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (104912333/200000000 : ℝ)*x 0 + (5665894529/10000000000 : ℝ)*x 1 + (-6888793/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (104912333/200000000 : ℝ)^8439 ≤ (42658460264119/100000000000000 : ℝ)^6391 := by
    have hnat : (104912333 : ℕ)^8439*100000000000000^6391 ≤ 42658460264119^6391*200000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104912333 200000000 42658460264119 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5665894529/10000000000 : ℝ)^8439 ≤ (47228398144769/100000000000000 : ℝ)^6391 := by
    have hnat : (5665894529 : ℕ)^8439*100000000000000^6391 ≤ 47228398144769^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665894529 10000000000 47228398144769 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6888793/39062500 : ℝ)^8439 ≤ (10113141577523/100000000000000 : ℝ)^6391 := by
    have hnat : (6888793 : ℕ)^8439*100000000000000^6391 ≤ 10113141577523^6391*39062500^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6888793 39062500 10113141577523 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(104912333/200000000 : ℝ), (5665894529/10000000000 : ℝ), (-6888793/39062500 : ℝ)] ![(42658460264119/100000000000000 : ℝ), (47228398144769/100000000000000 : ℝ), (10113141577523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(104912333/200000000 : ℝ)|^8439 ≤ (42658460264119/100000000000000 : ℝ)^6391
        have hw : |(104912333/200000000 : ℝ)|=(104912333/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5665894529/10000000000 : ℝ)|^8439 ≤ (47228398144769/100000000000000 : ℝ)^6391
        have hw : |(5665894529/10000000000 : ℝ)|=(5665894529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6888793/39062500 : ℝ)|^8439 ≤ (10113141577523/100000000000000 : ℝ)^6391
        have hw : |(-6888793/39062500 : ℝ)|=(6888793/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s1_7 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4309872153/10000000000 : ℝ)*x 0 + (5001043653/10000000000 : ℝ)*x 1 + (928461607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309872153/10000000000 : ℝ)^8439 ≤ (8227507323941/25000000000000 : ℝ)^6391 := by
    have hnat : (4309872153 : ℕ)^8439*25000000000000^6391 ≤ 8227507323941^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309872153 10000000000 8227507323941 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001043653/10000000000 : ℝ)^8439 ≤ (40052021308243/100000000000000 : ℝ)^6391 := by
    have hnat : (5001043653 : ℕ)^8439*100000000000000^6391 ≤ 40052021308243^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001043653 10000000000 40052021308243 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928461607/2500000000 : ℝ)^8439 ≤ (13518974686689/50000000000000 : ℝ)^6391 := by
    have hnat : (928461607 : ℕ)^8439*50000000000000^6391 ≤ 13518974686689^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928461607 2500000000 13518974686689 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309872153/10000000000 : ℝ), (5001043653/10000000000 : ℝ), (928461607/2500000000 : ℝ)] ![(8227507323941/25000000000000 : ℝ), (40052021308243/100000000000000 : ℝ), (13518974686689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309872153/10000000000 : ℝ)|^8439 ≤ (8227507323941/25000000000000 : ℝ)^6391
        have hw : |(4309872153/10000000000 : ℝ)|=(4309872153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001043653/10000000000 : ℝ)|^8439 ≤ (40052021308243/100000000000000 : ℝ)^6391
        have hw : |(5001043653/10000000000 : ℝ)|=(5001043653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(928461607/2500000000 : ℝ)|^8439 ≤ (13518974686689/50000000000000 : ℝ)^6391
        have hw : |(928461607/2500000000 : ℝ)|=(928461607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1246_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27421/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1553/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9991/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27421/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (417/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27421/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (417/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27421/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (417/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27421/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (417/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27421/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (417/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27421/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (417/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (417/50000 : ℝ) ^ (4219/1024 : ℝ) ≤ (136122688983/50000000000000000000 : ℝ) := by
    have hpowers : (417/50000 : ℝ)^4219 ≤ (136122688983/50000000000000000000 : ℝ)^1024 := by
      have hnat : (417 : ℕ)^4219*50000000000000000000^1024 ≤ 136122688983^1024*50000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        417 50000 136122688983 50000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (417/50000 : ℝ)) (X := (136122688983/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (27421/100000 : ℝ) ^ (4219/1024 : ℝ) ≤ (483991015892806343/100000000000000000000 : ℝ) := by
    have hpowers : (27421/100000 : ℝ)^4219 ≤ (483991015892806343/100000000000000000000 : ℝ)^1024 := by
      have hnat : (27421 : ℕ)^4219*100000000000000000000^1024 ≤ 483991015892806343^1024*100000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27421 100000 483991015892806343 100000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27421/100000 : ℝ)) (X := (483991015892806343/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000136122688983/25000000000000000000 : ℝ) ≤ (500000000660771/500000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (25000000136122688983/25000000000000000000 : ℝ)^1024 ≤ (500000000660771/500000000000000 : ℝ)^4219 := by
      have hnat : (25000000136122688983 : ℕ)^1024*500000000000000^4219 ≤ 500000000660771^4219*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000136122688983 25000000000000000000 500000000660771 500000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000000660771/500000000000000 : ℝ)) (X := (25000000136122688983/25000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100483991288138184309/100000000000000000000 : ℝ) ≤ (10011725560402361/10000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (100483991288138184309/100000000000000000000 : ℝ)^1024 ≤ (10011725560402361/10000000000000000 : ℝ)^4219 := by
      have hnat : (100483991288138184309 : ℕ)^1024*10000000000000000^4219 ≤ 10011725560402361^4219*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100483991288138184309 100000000000000000000 10011725560402361 10000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011725560402361/10000000000000000 : ℝ)) (X := (100483991288138184309/100000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50483991015892806343/50000000000000000000 : ℝ) ≤ (5011725553794651/5000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (50483991015892806343/50000000000000000000 : ℝ)^1024 ≤ (5011725553794651/5000000000000000 : ℝ)^4219 := by
      have hnat : (50483991015892806343 : ℕ)^1024*5000000000000000^4219 ≤ 5011725553794651^4219*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50483991015892806343 50000000000000000000 5011725553794651 5000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011725553794651/5000000000000000 : ℝ)) (X := (50483991015892806343/50000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(136122688983/50000000000000000000 : ℝ) ≤ ((8307826316832829811/8308437500000000000 : ℝ)+2*(11725547186941/2658700000000000 : ℝ)*(417/50000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (8307826316832829811/8308437500000000000 : ℝ)+2*(11725547186941/2658700000000000 : ℝ)*(417/50000 : ℝ)=(500000000660771/500000000000000 : ℝ) by norm_num, show 1+2*(136122688983/50000000000000000000 : ℝ)=(25000000136122688983/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(483991015892806343/100000000000000000000 : ℝ)+(136122688983/50000000000000000000 : ℝ) ≤ ((8307826316832829811/8308437500000000000 : ℝ)+(11725547186941/2658700000000000 : ℝ)*((27421/100000 : ℝ)+(417/50000 : ℝ)))^(4219/1024 : ℝ) := by
    rw [show (8307826316832829811/8308437500000000000 : ℝ)+(11725547186941/2658700000000000 : ℝ)*((27421/100000 : ℝ)+(417/50000 : ℝ))=(10011725560402361/10000000000000000 : ℝ) by norm_num, show 1+(483991015892806343/100000000000000000000 : ℝ)+(136122688983/50000000000000000000 : ℝ)=(100483991288138184309/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(483991015892806343/100000000000000000000 : ℝ) ≤ ((8307826316832829811/8308437500000000000 : ℝ)+2*(11725547186941/2658700000000000 : ℝ)*(27421/100000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (8307826316832829811/8308437500000000000 : ℝ)+2*(11725547186941/2658700000000000 : ℝ)*(27421/100000 : ℝ)=(5011725553794651/5000000000000000 : ℝ) by norm_num, show 1+2*(483991015892806343/100000000000000000000 : ℝ)=(50483991015892806343/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8307826316832829811/8308437500000000000 : ℝ)*(X 1 0+X 2 0)+(11725547186941/2658700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (417/50000 : ℝ)) (hi := (27421/100000 : ℝ)) (c := (8307826316832829811/8308437500000000000 : ℝ)) (alpha := (11725547186941/2658700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8307826316832829811/8308437500000000000 : ℝ)*(X 0 1+X 2 1)+(11725547186941/2658700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (417/50000 : ℝ)) (hi := (27421/100000 : ℝ)) (c := (8307826316832829811/8308437500000000000 : ℝ)) (alpha := (11725547186941/2658700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8307826316832829811/8308437500000000000 : ℝ)*(X 0 2+X 1 2)+(11725547186941/2658700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (417/50000 : ℝ)) (hi := (27421/100000 : ℝ)) (c := (8307826316832829811/8308437500000000000 : ℝ)) (alpha := (11725547186941/2658700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1028224067/5000000000 : ℝ)*X 0 0+(5674598399/10000000000 : ℝ)*X 0 1+(2511654253/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706719991/5000000000 : ℝ)*X 1 0+(-2406116693/10000000000 : ℝ)*X 1 1+(1255827157/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1353360023/2500000000 : ℝ)*X 2 0+(1255827139/2500000000 : ℝ)*X 2 1+(-1203058321/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((134640909/312500000 : ℝ)*X 0 0+(3696176113/10000000000 : ℝ)*X 0 1+(2509192229/5000000000 : ℝ)*X 0 2+(134640909/312500000 : ℝ)*X 1 0+(3696176113/10000000000 : ℝ)*X 1 1+(2509192229/5000000000 : ℝ)*X 1 2+(134640909/312500000 : ℝ)*X 2 0+(3696176113/10000000000 : ℝ)*X 2 1+(2509192229/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2057119593/10000000000 : ℝ)*X 0 0+(5031850251/10000000000 : ℝ)*X 0 1+(5665894493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5245616719/10000000000 : ℝ)*X 1 0+(-881765329/5000000000 : ℝ)*X 1 1+(5665894703/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((104912333/200000000 : ℝ)*X 2 0+(5665894529/10000000000 : ℝ)*X 2 1+(-6888793/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309872153/10000000000 : ℝ)*X 0 0+(5001043653/10000000000 : ℝ)*X 0 1+(928461607/2500000000 : ℝ)*X 0 2+(4309872153/10000000000 : ℝ)*X 1 0+(5001043653/10000000000 : ℝ)*X 1 1+(928461607/2500000000 : ℝ)*X 1 2+(4309872153/10000000000 : ℝ)*X 2 0+(5001043653/10000000000 : ℝ)*X 2 1+(928461607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2305240614685838192440883427/415421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27889499/50000000000000 : ℝ)*(base1) + (24399187/2000000000000 : ℝ)*(base19) + (1251158921/100000000000000 : ℝ)*(base23) + (130468353/100000000000000 : ℝ)*(upper3) + (19720283/12500000000000 : ℝ)*(upper5) + (572936586072989/50000000000000 : ℝ)*(major0) + (572936586072989/50000000000000 : ℝ)*(major1) + (572936586072989/50000000000000 : ℝ)*(major2) + (767710657117307/50000000000000 : ℝ)*(sp0) + (95964206995451/6250000000000 : ℝ)*(sp1) + (383856820181911/25000000000000 : ℝ)*(sp2) + (378157006657833/50000000000000 : ℝ)*(sp3) + (7273430949/100000000000000 : ℝ)*(sp4) + (711667773/20000000000000 : ℝ)*(sp7) + (75631762743353/10000000000000 : ℝ)*(f.failure) + (767714265943283/50000000000000 : ℝ)*(f.sum) + (8838806633451/66467500000000000000000000000 : ℝ)*base66 + (65699560037432051/103855468750000000000000000000000 : ℝ)*base67 + (4258004920085868829/415421875000000000000000000000000 : ℝ)*base69 + (1815801575898693671/415421875000000000000000000000000 : ℝ)*base72 + (38261068599727/132935000000000000000000000000 : ℝ)*base74 + (347885087178463301/103855468750000000000000000000000 : ℝ)*base75 + (2174760423682056329/415421875000000000000000000000000 : ℝ)*base77 + (2282030674368900079/415421875000000000000000000000000 : ℝ)*base79 + (353915093420149/66467500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (9078463/1000000000000000000000 : ℝ)*base89 + (9078463/1000000000000000000000 : ℝ)*base91 + (9078463/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (428483854153532184450672663/51927734375000000000000000000000 : ℝ) := by norm_num
    linear_combination (73917101/100000000000000 : ℝ)*(base1) + (328111869/20000000000000 : ℝ)*(base19) + (798033827/50000000000000 : ℝ)*(base23) + (505621/250000000000 : ℝ)*(upper3) + (182429443/100000000000000 : ℝ)*(upper5) + (1177029356801379/100000000000000 : ℝ)*(major0) + (1177029356801379/100000000000000 : ℝ)*(major1) + (1177029356801379/100000000000000 : ℝ)*(major2) + (3890742223/50000000000000 : ℝ)*(sp1) + (7039259891/100000000000000 : ℝ)*(sp2) + (1577176679299741/100000000000000 : ℝ)*(sp4) + (1577167183338849/100000000000000 : ℝ)*(sp5) + (788583985027547/50000000000000 : ℝ)*(sp6) + (388440879625813/50000000000000 : ℝ)*(sp7) + (776881833168727/100000000000000 : ℝ)*(f.failure) + (19714707567283/1250000000000 : ℝ)*(f.sum) + (41452626248841/33233750000000000000000000000 : ℝ)*base65 + (1096925228952318747/415421875000000000000000000000000 : ℝ)*base67 + (141910438170068747/415421875000000000000000000000000 : ℝ)*base69 + (1923950249923506247/415421875000000000000000000000000 : ℝ)*base71 + (20061276481409/132935000000000000000000000000 : ℝ)*base73 + (3874646049621412497/415421875000000000000000000000000 : ℝ)*base75 + (45517216585986499/3245483398437500000000000000000 : ℝ)*base77 + (1994956778664464061/207710937500000000000000000000000 : ℝ)*base79 + (372747171365351/132935000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (57176783/10000000000000000000000 : ℝ)*base90 + (57176783/10000000000000000000000 : ℝ)*base92 + (57176783/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1246_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27421/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (417/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1553/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9991/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1246_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1246_s2_0 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2104288947/10000000000 : ℝ)*x 0 + (2746056637/5000000000 : ℝ)*x 1 + (2587639987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2104288947/10000000000 : ℝ)^8439 ≤ (3192523265293/25000000000000 : ℝ)^6391 := by
    have hnat : (2104288947 : ℕ)^8439*25000000000000^6391 ≤ 3192523265293^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2104288947 10000000000 3192523265293 25000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746056637/5000000000 : ℝ)^8439 ≤ (1416409597763/3125000000000 : ℝ)^6391 := by
    have hnat : (2746056637 : ℕ)^8439*3125000000000^6391 ≤ 1416409597763^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746056637 5000000000 1416409597763 3125000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2587639987/5000000000 : ℝ)^8439 ≤ (1676191991859/4000000000000 : ℝ)^6391 := by
    have hnat : (2587639987 : ℕ)^8439*4000000000000^6391 ≤ 1676191991859^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587639987 5000000000 1676191991859 4000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2104288947/10000000000 : ℝ), (2746056637/5000000000 : ℝ), (2587639987/5000000000 : ℝ)] ![(3192523265293/25000000000000 : ℝ), (1416409597763/3125000000000 : ℝ), (1676191991859/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2104288947/10000000000 : ℝ)|^8439 ≤ (3192523265293/25000000000000 : ℝ)^6391
        have hw : |(-2104288947/10000000000 : ℝ)|=(2104288947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746056637/5000000000 : ℝ)|^8439 ≤ (1416409597763/3125000000000 : ℝ)^6391
        have hw : |(2746056637/5000000000 : ℝ)|=(2746056637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2587639987/5000000000 : ℝ)|^8439 ≤ (1676191991859/4000000000000 : ℝ)^6391
        have hw : |(2587639987/5000000000 : ℝ)|=(2587639987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s2_1 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369524983/10000000000 : ℝ)*x 0 + (-2268383659/10000000000 : ℝ)*x 1 + (5175280017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369524983/10000000000 : ℝ)^8439 ≤ (43994019699347/100000000000000 : ℝ)^6391 := by
    have hnat : (5369524983 : ℕ)^8439*100000000000000^6391 ≤ 43994019699347^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369524983 10000000000 43994019699347 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2268383659/10000000000 : ℝ)^8439 ≤ (2820236006921/20000000000000 : ℝ)^6391 := by
    have hnat : (2268383659 : ℕ)^8439*20000000000000^6391 ≤ 2820236006921^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2268383659 10000000000 2820236006921 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5175280017/10000000000 : ℝ)^8439 ≤ (1309525008007/3125000000000 : ℝ)^6391 := by
    have hnat : (5175280017 : ℕ)^8439*3125000000000^6391 ≤ 1309525008007^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175280017 10000000000 1309525008007 3125000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369524983/10000000000 : ℝ), (-2268383659/10000000000 : ℝ), (5175280017/10000000000 : ℝ)] ![(43994019699347/100000000000000 : ℝ), (2820236006921/20000000000000 : ℝ), (1309525008007/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369524983/10000000000 : ℝ)|^8439 ≤ (43994019699347/100000000000000 : ℝ)^6391
        have hw : |(5369524983/10000000000 : ℝ)|=(5369524983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2268383659/10000000000 : ℝ)|^8439 ≤ (2820236006921/20000000000000 : ℝ)^6391
        have hw : |(-2268383659/10000000000 : ℝ)|=(2268383659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5175280017/10000000000 : ℝ)|^8439 ≤ (1309525008007/3125000000000 : ℝ)^6391
        have hw : |(5175280017/10000000000 : ℝ)|=(5175280017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s2_2 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5369524849/10000000000 : ℝ)*x 0 + (1293820029/2500000000 : ℝ)*x 1 + (-1134191853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369524849/10000000000 : ℝ)^8439 ≤ (351952145997/800000000000 : ℝ)^6391 := by
    have hnat : (5369524849 : ℕ)^8439*800000000000^6391 ≤ 351952145997^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369524849 10000000000 351952145997 800000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293820029/2500000000 : ℝ)^8439 ≤ (8380960262943/20000000000000 : ℝ)^6391 := by
    have hnat : (1293820029 : ℕ)^8439*20000000000000^6391 ≤ 8380960262943^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293820029 2500000000 8380960262943 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134191853/5000000000 : ℝ)^8439 ≤ (7050590210201/50000000000000 : ℝ)^6391 := by
    have hnat : (1134191853 : ℕ)^8439*50000000000000^6391 ≤ 7050590210201^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134191853 5000000000 7050590210201 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369524849/10000000000 : ℝ), (1293820029/2500000000 : ℝ), (-1134191853/5000000000 : ℝ)] ![(351952145997/800000000000 : ℝ), (8380960262943/20000000000000 : ℝ), (7050590210201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369524849/10000000000 : ℝ)|^8439 ≤ (351952145997/800000000000 : ℝ)^6391
        have hw : |(5369524849/10000000000 : ℝ)|=(5369524849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293820029/2500000000 : ℝ)|^8439 ≤ (8380960262943/20000000000000 : ℝ)^6391
        have hw : |(1293820029/2500000000 : ℝ)|=(1293820029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134191853/5000000000 : ℝ)|^8439 ≤ (7050590210201/50000000000000 : ℝ)^6391
        have hw : |(-1134191853/5000000000 : ℝ)|=(1134191853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s2_3 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4341563533/10000000000 : ℝ)*x 0 + (403148331/1000000000 : ℝ)*x 1 + (934939661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341563533/10000000000 : ℝ)^8439 ≤ (830748664869/2500000000000 : ℝ)^6391 := by
    have hnat : (4341563533 : ℕ)^8439*2500000000000^6391 ≤ 830748664869^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341563533 10000000000 830748664869 2500000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403148331/1000000000 : ℝ)^8439 ≤ (301325463003/1000000000000 : ℝ)^6391 := by
    have hnat : (403148331 : ℕ)^8439*1000000000000^6391 ≤ 301325463003^6391*1000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403148331 1000000000 301325463003 1000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (934939661/2000000000 : ℝ)^8439 ≤ (36637507096917/100000000000000 : ℝ)^6391 := by
    have hnat : (934939661 : ℕ)^8439*100000000000000^6391 ≤ 36637507096917^6391*2000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      934939661 2000000000 36637507096917 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341563533/10000000000 : ℝ), (403148331/1000000000 : ℝ), (934939661/2000000000 : ℝ)] ![(830748664869/2500000000000 : ℝ), (301325463003/1000000000000 : ℝ), (36637507096917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341563533/10000000000 : ℝ)|^8439 ≤ (830748664869/2500000000000 : ℝ)^6391
        have hw : |(4341563533/10000000000 : ℝ)|=(4341563533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403148331/1000000000 : ℝ)|^8439 ≤ (301325463003/1000000000000 : ℝ)^6391
        have hw : |(403148331/1000000000 : ℝ)|=(403148331/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(934939661/2000000000 : ℝ)|^8439 ≤ (36637507096917/100000000000000 : ℝ)^6391
        have hw : |(934939661/2000000000 : ℝ)|=(934939661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s2_4 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-420873309/2000000000 : ℝ)*x 0 + (207092447/400000000 : ℝ)*x 1 + (2745031537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420873309/2000000000 : ℝ)^8439 ≤ (319267872003/2500000000000 : ℝ)^6391 := by
    have hnat : (420873309 : ℕ)^8439*2500000000000^6391 ≤ 319267872003^6391*2000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420873309 2000000000 319267872003 2500000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207092447/400000000 : ℝ)^8439 ≤ (41926518420103/100000000000000 : ℝ)^6391 := by
    have hnat : (207092447 : ℕ)^8439*100000000000000^6391 ≤ 41926518420103^6391*400000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207092447 400000000 41926518420103 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745031537/5000000000 : ℝ)^8439 ≤ (45302766685819/100000000000000 : ℝ)^6391 := by
    have hnat : (2745031537 : ℕ)^8439*100000000000000^6391 ≤ 45302766685819^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745031537 5000000000 45302766685819 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-420873309/2000000000 : ℝ), (207092447/400000000 : ℝ), (2745031537/5000000000 : ℝ)] ![(319267872003/2500000000000 : ℝ), (41926518420103/100000000000000 : ℝ), (45302766685819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-420873309/2000000000 : ℝ)|^8439 ≤ (319267872003/2500000000000 : ℝ)^6391
        have hw : |(-420873309/2000000000 : ℝ)|=(420873309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207092447/400000000 : ℝ)|^8439 ≤ (41926518420103/100000000000000 : ℝ)^6391
        have hw : |(207092447/400000000 : ℝ)|=(207092447/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745031537/5000000000 : ℝ)|^8439 ≤ (45302766685819/100000000000000 : ℝ)^6391
        have hw : |(2745031537/5000000000 : ℝ)|=(2745031537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s2_5 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5288594087/10000000000 : ℝ)*x 0 + (-1953600369/10000000000 : ℝ)*x 1 + (5490063119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288594087/10000000000 : ℝ)^8439 ≤ (43120564545637/100000000000000 : ℝ)^6391 := by
    have hnat : (5288594087 : ℕ)^8439*100000000000000^6391 ≤ 43120564545637^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288594087 10000000000 43120564545637 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1953600369/10000000000 : ℝ)^8439 ≤ (2315333652569/20000000000000 : ℝ)^6391 := by
    have hnat : (1953600369 : ℕ)^8439*20000000000000^6391 ≤ 2315333652569^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953600369 10000000000 2315333652569 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490063119/10000000000 : ℝ)^8439 ≤ (22651383588071/50000000000000 : ℝ)^6391 := by
    have hnat : (5490063119 : ℕ)^8439*50000000000000^6391 ≤ 22651383588071^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490063119 10000000000 22651383588071 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288594087/10000000000 : ℝ), (-1953600369/10000000000 : ℝ), (5490063119/10000000000 : ℝ)] ![(43120564545637/100000000000000 : ℝ), (2315333652569/20000000000000 : ℝ), (22651383588071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288594087/10000000000 : ℝ)|^8439 ≤ (43120564545637/100000000000000 : ℝ)^6391
        have hw : |(5288594087/10000000000 : ℝ)|=(5288594087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1953600369/10000000000 : ℝ)|^8439 ≤ (2315333652569/20000000000000 : ℝ)^6391
        have hw : |(-1953600369/10000000000 : ℝ)|=(1953600369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490063119/10000000000 : ℝ)|^8439 ≤ (22651383588071/50000000000000 : ℝ)^6391
        have hw : |(5490063119/10000000000 : ℝ)|=(5490063119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s2_6 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644297123/5000000000 : ℝ)*x 0 + (5490063207/10000000000 : ℝ)*x 1 + (-488400007/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644297123/5000000000 : ℝ)^8439 ≤ (21560283128739/50000000000000 : ℝ)^6391 := by
    have hnat : (2644297123 : ℕ)^8439*50000000000000^6391 ≤ 21560283128739^6391*5000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644297123 5000000000 21560283128739 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490063207/10000000000 : ℝ)^8439 ≤ (9060553626999/20000000000000 : ℝ)^6391 := by
    have hnat : (5490063207 : ℕ)^8439*20000000000000^6391 ≤ 9060553626999^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490063207 10000000000 9060553626999 20000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (488400007/2500000000 : ℝ)^8439 ≤ (723541599663/6250000000000 : ℝ)^6391 := by
    have hnat : (488400007 : ℕ)^8439*6250000000000^6391 ≤ 723541599663^6391*2500000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      488400007 2500000000 723541599663 6250000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644297123/5000000000 : ℝ), (5490063207/10000000000 : ℝ), (-488400007/2500000000 : ℝ)] ![(21560283128739/50000000000000 : ℝ), (9060553626999/20000000000000 : ℝ), (723541599663/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644297123/5000000000 : ℝ)|^8439 ≤ (21560283128739/50000000000000 : ℝ)^6391
        have hw : |(2644297123/5000000000 : ℝ)|=(2644297123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490063207/10000000000 : ℝ)|^8439 ≤ (9060553626999/20000000000000 : ℝ)^6391
        have hw : |(5490063207/10000000000 : ℝ)|=(5490063207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-488400007/2500000000 : ℝ)|^8439 ≤ (723541599663/6250000000000 : ℝ)^6391
        have hw : |(-488400007/2500000000 : ℝ)|=(488400007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1246_s2_7 (p : ℝ) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4341720547/10000000000 : ℝ)*x 0 + (4670574997/10000000000 : ℝ)*x 1 + (4035644839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4341720547/10000000000 : ℝ)^8439 ≤ (16615766741873/50000000000000 : ℝ)^6391 := by
    have hnat : (4341720547 : ℕ)^8439*50000000000000^6391 ≤ 16615766741873^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4341720547 10000000000 16615766741873 50000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4670574997/10000000000 : ℝ)^8439 ≤ (1829742069823/5000000000000 : ℝ)^6391 := by
    have hnat : (4670574997 : ℕ)^8439*5000000000000^6391 ≤ 1829742069823^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4670574997 10000000000 1829742069823 5000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4035644839/10000000000 : ℝ)^8439 ≤ (30173625111607/100000000000000 : ℝ)^6391 := by
    have hnat : (4035644839 : ℕ)^8439*100000000000000^6391 ≤ 30173625111607^6391*10000000000^8439 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035644839 10000000000 30173625111607 100000000000000 8439 6391 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8439/2048 : ℝ)) 8439 6391 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4341720547/10000000000 : ℝ), (4670574997/10000000000 : ℝ), (4035644839/10000000000 : ℝ)] ![(16615766741873/50000000000000 : ℝ), (1829742069823/5000000000000 : ℝ), (30173625111607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4341720547/10000000000 : ℝ)|^8439 ≤ (16615766741873/50000000000000 : ℝ)^6391
        have hw : |(4341720547/10000000000 : ℝ)|=(4341720547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4670574997/10000000000 : ℝ)|^8439 ≤ (1829742069823/5000000000000 : ℝ)^6391
        have hw : |(4670574997/10000000000 : ℝ)|=(4670574997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4035644839/10000000000 : ℝ)|^8439 ≤ (30173625111607/100000000000000 : ℝ)^6391
        have hw : |(4035644839/10000000000 : ℝ)|=(4035644839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1246_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1553/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1903/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16213/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1553/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9991/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1553/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1553/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9991/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1553/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1553/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9991/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1553/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1553/25000 : ℝ) ^ (4219/1024 : ℝ) ≤ (533263855153189/50000000000000000000 : ℝ) := by
    have hpowers : (1553/25000 : ℝ)^4219 ≤ (533263855153189/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1553 : ℕ)^4219*50000000000000000000^1024 ≤ 533263855153189^1024*25000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1553 25000 533263855153189 50000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1553/25000 : ℝ)) (X := (533263855153189/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (9991/50000 : ℝ) ^ (4219/1024 : ℝ) ≤ (131386437403794381/100000000000000000000 : ℝ) := by
    have hpowers : (9991/50000 : ℝ)^4219 ≤ (131386437403794381/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9991 : ℕ)^4219*100000000000000000000^1024 ≤ 131386437403794381^1024*50000^4219 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9991 50000 131386437403794381 100000000000000000000 4219 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9991/50000 : ℝ)) (X := (131386437403794381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000533263855153189/25000000000000000000 : ℝ) ≤ (1000005177129911/1000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (25000533263855153189/25000000000000000000 : ℝ)^1024 ≤ (1000005177129911/1000000000000000 : ℝ)^4219 := by
      have hnat : (25000533263855153189 : ℕ)^1024*1000000000000000^4219 ≤ 1000005177129911^4219*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000533263855153189 25000000000000000000 1000005177129911 1000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000005177129911/1000000000000000 : ℝ)) (X := (25000533263855153189/25000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100132452965114100759/100000000000000000000 : ℝ) ≤ (2000642635061291/2000000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (100132452965114100759/100000000000000000000 : ℝ)^1024 ≤ (2000642635061291/2000000000000000 : ℝ)^4219 := by
      have hnat : (100132452965114100759 : ℕ)^1024*2000000000000000^4219 ≤ 2000642635061291^4219*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100132452965114100759 100000000000000000000 2000642635061291 2000000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000642635061291/2000000000000000 : ℝ)) (X := (100132452965114100759/100000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50131386437403794381/50000000000000000000 : ℝ) ≤ (50031872896569/50000000000000 : ℝ) ^ (4219/1024 : ℝ) := by
    have hpowers : (50131386437403794381/50000000000000000000 : ℝ)^1024 ≤ (50031872896569/50000000000000 : ℝ)^4219 := by
      have hnat : (50131386437403794381 : ℕ)^1024*50000000000000^4219 ≤ 50031872896569^4219*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50131386437403794381 50000000000000000000 50031872896569 50000000000000 1024 4219 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50031872896569/50000000000000 : ℝ)) (X := (50131386437403794381/50000000000000000000 : ℝ)) (by norm_num) 4219 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(533263855153189/50000000000000000000 : ℝ) ≤ ((6883071780370074521/6885000000000000000 : ℝ)+2*(632280801469/275400000000000 : ℝ)*(1553/25000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (6883071780370074521/6885000000000000000 : ℝ)+2*(632280801469/275400000000000 : ℝ)*(1553/25000 : ℝ)=(1000005177129911/1000000000000000 : ℝ) by norm_num, show 1+2*(533263855153189/50000000000000000000 : ℝ)=(25000533263855153189/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(131386437403794381/100000000000000000000 : ℝ)+(533263855153189/50000000000000000000 : ℝ) ≤ ((6883071780370074521/6885000000000000000 : ℝ)+(632280801469/275400000000000 : ℝ)*((9991/50000 : ℝ)+(1553/25000 : ℝ)))^(4219/1024 : ℝ) := by
    rw [show (6883071780370074521/6885000000000000000 : ℝ)+(632280801469/275400000000000 : ℝ)*((9991/50000 : ℝ)+(1553/25000 : ℝ))=(2000642635061291/2000000000000000 : ℝ) by norm_num, show 1+(131386437403794381/100000000000000000000 : ℝ)+(533263855153189/50000000000000000000 : ℝ)=(100132452965114100759/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(131386437403794381/100000000000000000000 : ℝ) ≤ ((6883071780370074521/6885000000000000000 : ℝ)+2*(632280801469/275400000000000 : ℝ)*(9991/50000 : ℝ))^(4219/1024 : ℝ) := by
    rw [show (6883071780370074521/6885000000000000000 : ℝ)+2*(632280801469/275400000000000 : ℝ)*(9991/50000 : ℝ)=(50031872896569/50000000000000 : ℝ) by norm_num, show 1+2*(131386437403794381/100000000000000000000 : ℝ)=(50131386437403794381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6883071780370074521/6885000000000000000 : ℝ)*(X 1 0+X 2 0)+(632280801469/275400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (1553/25000 : ℝ)) (hi := (9991/50000 : ℝ)) (c := (6883071780370074521/6885000000000000000 : ℝ)) (alpha := (632280801469/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6883071780370074521/6885000000000000000 : ℝ)*(X 0 1+X 2 1)+(632280801469/275400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (1553/25000 : ℝ)) (hi := (9991/50000 : ℝ)) (c := (6883071780370074521/6885000000000000000 : ℝ)) (alpha := (632280801469/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6883071780370074521/6885000000000000000 : ℝ)*(X 0 2+X 1 2)+(632280801469/275400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4219/1024 : ℝ)) (lo := (1553/25000 : ℝ)) (hi := (9991/50000 : ℝ)) (c := (6883071780370074521/6885000000000000000 : ℝ)) (alpha := (632280801469/275400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2104288947/10000000000 : ℝ)*X 0 0+(2746056637/5000000000 : ℝ)*X 0 1+(2587639987/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369524983/10000000000 : ℝ)*X 1 0+(-2268383659/10000000000 : ℝ)*X 1 1+(5175280017/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369524849/10000000000 : ℝ)*X 2 0+(1293820029/2500000000 : ℝ)*X 2 1+(-1134191853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4341563533/10000000000 : ℝ)*X 0 0+(403148331/1000000000 : ℝ)*X 0 1+(934939661/2000000000 : ℝ)*X 0 2+(4341563533/10000000000 : ℝ)*X 1 0+(403148331/1000000000 : ℝ)*X 1 1+(934939661/2000000000 : ℝ)*X 1 2+(4341563533/10000000000 : ℝ)*X 2 0+(403148331/1000000000 : ℝ)*X 2 1+(934939661/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-420873309/2000000000 : ℝ)*X 0 0+(207092447/400000000 : ℝ)*X 0 1+(2745031537/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288594087/10000000000 : ℝ)*X 1 0+(-1953600369/10000000000 : ℝ)*X 1 1+(5490063119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644297123/5000000000 : ℝ)*X 2 0+(5490063207/10000000000 : ℝ)*X 2 1+(-488400007/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4341720547/10000000000 : ℝ)*X 0 0+(4670574997/10000000000 : ℝ)*X 0 1+(4035644839/10000000000 : ℝ)*X 0 2+(4341720547/10000000000 : ℝ)*X 1 0+(4670574997/10000000000 : ℝ)*X 1 1+(4035644839/10000000000 : ℝ)*X 1 2+(4341720547/10000000000 : ℝ)*X 2 0+(4670574997/10000000000 : ℝ)*X 2 1+(4035644839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1246_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (601401801761595412865977453/57375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2030020791/100000000000000 : ℝ)*(base19) + (1819821693/100000000000000 : ℝ)*(base23) + (70572801/100000000000000 : ℝ)*(lower2) + (306932157/100000000000000 : ℝ)*(upper3) + (73296761/50000000000000 : ℝ)*(upper5) + (1177748270557093/50000000000000 : ℝ)*(major0) + (1177748270557093/50000000000000 : ℝ)*(major1) + (1177748270557093/50000000000000 : ℝ)*(major2) + (3156258253524939/100000000000000 : ℝ)*(sp0) + (3156278018449129/100000000000000 : ℝ)*(sp1) + (3156278228648227/100000000000000 : ℝ)*(sp2) + (777350282725017/50000000000000 : ℝ)*(sp3) + (21794944981/100000000000000 : ℝ)*(sp4) + (12118910127/100000000000000 : ℝ)*(sp7) + (1554712684360161/100000000000000 : ℝ)*(f.failure) + (19726750302937/625000000000 : ℝ)*(f.sum) + (4770613013597/1721250000000000000000000000 : ℝ)*base66 + (589433738324815849/114750000000000000000000000000000 : ℝ)*base68 + (110937151125934151/114750000000000000000000000000000 : ℝ)*base69 + (554973832024684151/114750000000000000000000000000000 : ℝ)*base71 + (5919464189363/6885000000000000000000000000 : ℝ)*base74 + (219399642365815849/114750000000000000000000000000000 : ℝ)*base76 + (1220920452586315849/114750000000000000000000000000000 : ℝ)*base78 + (284009558147065849/114750000000000000000000000000000 : ℝ)*base80 + (2520897170227/430312500000000000000000000 : ℝ)*base81 + (30166231/10000000000000000000000 : ℝ)*base89 + (30166231/10000000000000000000000 : ℝ)*base91 + (30166231/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (306467889782177182928883721/38250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2000227553/100000000000000 : ℝ)*(base19) + (2242261097/100000000000000 : ℝ)*(base23) + (3600279/12500000000000 : ℝ)*(upper2) + (133897531/50000000000000 : ℝ)*(upper3) + (31475653/20000000000000 : ℝ)*(upper5) + (2386199304265603/100000000000000 : ℝ)*(major0) + (2386199304265603/100000000000000 : ℝ)*(major1) + (2386199304265603/100000000000000 : ℝ)*(major2) + (257591389/1250000000000 : ℝ)*(sp1) + (1063317647/4000000000000 : ℝ)*(sp2) + (319742072590983/10000000000000 : ℝ)*(sp4) + (3197398118371157/100000000000000 : ℝ)*(sp5) + (1598695950353779/50000000000000 : ℝ)*(sp6) + (393744403886739/25000000000000 : ℝ)*(sp7) + (393744403886739/25000000000000 : ℝ)*(f.failure) + (319742072590983/10000000000000 : ℝ)*(f.sum) + (70928211966667/13770000000000000000000000000 : ℝ)*base65 + (555260959649941279/229500000000000000000000000000000 : ℝ)*base68 + (452804843648941279/229500000000000000000000000000000 : ℝ)*base70 + (688406570935441279/229500000000000000000000000000000 : ℝ)*base72 + (97476131152177/13770000000000000000000000000 : ℝ)*base73 + (1852830648187441279/229500000000000000000000000000000 : ℝ)*base76 + (468271312156558721/229500000000000000000000000000000 : ℝ)*base77 + (749115014748058721/229500000000000000000000000000000 : ℝ)*base79 + (110605278230107/13770000000000000000000000000 : ℝ)*base81 + (10716331/2500000000000000000000 : ℝ)*base90 + (10716331/2500000000000000000000 : ℝ)*base92 + (10716331/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1246_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9991/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1553/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1903/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16213/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1246_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1246_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1903/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16213/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1246_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1246_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1246_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4219/1024 : ℝ) ≤ p) (hpb : p ≤ (8439/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151506871/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1903/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16213/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1246_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
