-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1213_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:07:58.940774+00:00
-- url     : https://prove2.me/submissions/4b90d627-b112-4a61-9d09-3f2c40ec3fda

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
theorem support_rectangle_w1213_s0_0 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1869541277/10000000000 : ℝ)*x 0 + (1207613063/2000000000 : ℝ)*x 1 + (4789385711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1869541277/10000000000 : ℝ)^4203 ≤ (10893083126573/100000000000000 : ℝ)^3179 := by
    have hnat : (1869541277 : ℕ)^4203*100000000000000^3179 ≤ 10893083126573^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1869541277 10000000000 10893083126573 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1207613063/2000000000 : ℝ)^4203 ≤ (51324171867261/100000000000000 : ℝ)^3179 := by
    have hnat : (1207613063 : ℕ)^4203*100000000000000^3179 ≤ 51324171867261^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207613063 2000000000 51324171867261 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4789385711/10000000000 : ℝ)^4203 ≤ (60452391981/160000000000 : ℝ)^3179 := by
    have hnat : (4789385711 : ℕ)^4203*160000000000^3179 ≤ 60452391981^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789385711 10000000000 60452391981 160000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1869541277/10000000000 : ℝ), (1207613063/2000000000 : ℝ), (4789385711/10000000000 : ℝ)] ![(10893083126573/100000000000000 : ℝ), (51324171867261/100000000000000 : ℝ), (60452391981/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1869541277/10000000000 : ℝ)|^4203 ≤ (10893083126573/100000000000000 : ℝ)^3179
        have hw : |(-1869541277/10000000000 : ℝ)|=(1869541277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1207613063/2000000000 : ℝ)|^4203 ≤ (51324171867261/100000000000000 : ℝ)^3179
        have hw : |(1207613063/2000000000 : ℝ)|=(1207613063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4789385711/10000000000 : ℝ)|^4203 ≤ (60452391981/160000000000 : ℝ)^3179
        have hw : |(4789385711/10000000000 : ℝ)|=(4789385711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s0_1 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5512793343/10000000000 : ℝ)*x 0 + (-2584171569/10000000000 : ℝ)*x 1 + (1197346421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5512793343/10000000000 : ℝ)^4203 ≤ (45505506567057/100000000000000 : ℝ)^3179 := by
    have hnat : (5512793343 : ℕ)^4203*100000000000000^3179 ≤ 45505506567057^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5512793343 10000000000 45505506567057 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2584171569/10000000000 : ℝ)^4203 ≤ (16711748706131/100000000000000 : ℝ)^3179 := by
    have hnat : (2584171569 : ℕ)^4203*100000000000000^3179 ≤ 16711748706131^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584171569 10000000000 16711748706131 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1197346421/2500000000 : ℝ)^4203 ≤ (9445686176629/25000000000000 : ℝ)^3179 := by
    have hnat : (1197346421 : ℕ)^4203*25000000000000^3179 ≤ 9445686176629^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1197346421 2500000000 9445686176629 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5512793343/10000000000 : ℝ), (-2584171569/10000000000 : ℝ), (1197346421/2500000000 : ℝ)] ![(45505506567057/100000000000000 : ℝ), (16711748706131/100000000000000 : ℝ), (9445686176629/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5512793343/10000000000 : ℝ)|^4203 ≤ (45505506567057/100000000000000 : ℝ)^3179
        have hw : |(5512793343/10000000000 : ℝ)|=(5512793343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2584171569/10000000000 : ℝ)|^4203 ≤ (16711748706131/100000000000000 : ℝ)^3179
        have hw : |(-2584171569/10000000000 : ℝ)|=(2584171569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1197346421/2500000000 : ℝ)|^4203 ≤ (9445686176629/25000000000000 : ℝ)^3179
        have hw : |(1197346421/2500000000 : ℝ)|=(1197346421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s0_2 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2756396663/5000000000 : ℝ)*x 0 + (598673213/1250000000 : ℝ)*x 1 + (-2584171567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756396663/5000000000 : ℝ)^4203 ≤ (45505506381529/100000000000000 : ℝ)^3179 := by
    have hnat : (2756396663 : ℕ)^4203*100000000000000^3179 ≤ 45505506381529^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756396663 5000000000 45505506381529 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598673213/1250000000 : ℝ)^4203 ≤ (9445686228779/25000000000000 : ℝ)^3179 := by
    have hnat : (598673213 : ℕ)^4203*25000000000000^3179 ≤ 9445686228779^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598673213 1250000000 9445686228779 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2584171567/10000000000 : ℝ)^4203 ≤ (16711748689031/100000000000000 : ℝ)^3179 := by
    have hnat : (2584171567 : ℕ)^4203*100000000000000^3179 ≤ 16711748689031^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2584171567 10000000000 16711748689031 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756396663/5000000000 : ℝ), (598673213/1250000000 : ℝ), (-2584171567/10000000000 : ℝ)] ![(45505506381529/100000000000000 : ℝ), (9445686228779/25000000000000 : ℝ), (16711748689031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756396663/5000000000 : ℝ)|^4203 ≤ (45505506381529/100000000000000 : ℝ)^3179
        have hw : |(2756396663/5000000000 : ℝ)|=(2756396663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598673213/1250000000 : ℝ)|^4203 ≤ (9445686228779/25000000000000 : ℝ)^3179
        have hw : |(598673213/1250000000 : ℝ)|=(598673213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2584171567/10000000000 : ℝ)|^4203 ≤ (16711748689031/100000000000000 : ℝ)^3179
        have hw : |(-2584171567/10000000000 : ℝ)|=(2584171567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s0_3 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (839061749/2000000000 : ℝ)*x 0 + (3118015143/10000000000 : ℝ)*x 1 + (5636873457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (839061749/2000000000 : ℝ)^4203 ≤ (7928498783241/25000000000000 : ℝ)^3179 := by
    have hnat : (839061749 : ℕ)^4203*25000000000000^3179 ≤ 7928498783241^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      839061749 2000000000 7928498783241 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3118015143/10000000000 : ℝ)^4203 ≤ (167355274327/781250000000 : ℝ)^3179 := by
    have hnat : (3118015143 : ℕ)^4203*781250000000^3179 ≤ 167355274327^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118015143 10000000000 167355274327 781250000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5636873457/10000000000 : ℝ)^4203 ≤ (46864529736617/100000000000000 : ℝ)^3179 := by
    have hnat : (5636873457 : ℕ)^4203*100000000000000^3179 ≤ 46864529736617^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5636873457 10000000000 46864529736617 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(839061749/2000000000 : ℝ), (3118015143/10000000000 : ℝ), (5636873457/10000000000 : ℝ)] ![(7928498783241/25000000000000 : ℝ), (167355274327/781250000000 : ℝ), (46864529736617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(839061749/2000000000 : ℝ)|^4203 ≤ (7928498783241/25000000000000 : ℝ)^3179
        have hw : |(839061749/2000000000 : ℝ)|=(839061749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3118015143/10000000000 : ℝ)|^4203 ≤ (167355274327/781250000000 : ℝ)^3179
        have hw : |(3118015143/10000000000 : ℝ)|=(3118015143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5636873457/10000000000 : ℝ)|^4203 ≤ (46864529736617/100000000000000 : ℝ)^3179
        have hw : |(5636873457/10000000000 : ℝ)|=(5636873457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s0_4 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-937240829/5000000000 : ℝ)*x 0 + (602695013/1250000000 : ℝ)*x 1 + (300237739/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (937240829/5000000000 : ℝ)^4203 ≤ (10931157235849/100000000000000 : ℝ)^3179 := by
    have hnat : (937240829 : ℕ)^4203*100000000000000^3179 ≤ 10931157235849^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937240829 5000000000 10931157235849 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602695013/1250000000 : ℝ)^4203 ≤ (38118685083109/100000000000000 : ℝ)^3179 := by
    have hnat : (602695013 : ℕ)^4203*100000000000000^3179 ≤ 38118685083109^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602695013 1250000000 38118685083109 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300237739/500000000 : ℝ)^4203 ≤ (25475078836629/50000000000000 : ℝ)^3179 := by
    have hnat : (300237739 : ℕ)^4203*50000000000000^3179 ≤ 25475078836629^3179*500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300237739 500000000 25475078836629 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-937240829/5000000000 : ℝ), (602695013/1250000000 : ℝ), (300237739/500000000 : ℝ)] ![(10931157235849/100000000000000 : ℝ), (38118685083109/100000000000000 : ℝ), (25475078836629/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-937240829/5000000000 : ℝ)|^4203 ≤ (10931157235849/100000000000000 : ℝ)^3179
        have hw : |(-937240829/5000000000 : ℝ)|=(937240829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(602695013/1250000000 : ℝ)|^4203 ≤ (38118685083109/100000000000000 : ℝ)^3179
        have hw : |(602695013/1250000000 : ℝ)|=(602695013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300237739/500000000 : ℝ)|^4203 ≤ (25475078836629/50000000000000 : ℝ)^3179
        have hw : |(300237739/500000000 : ℝ)|=(300237739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s0_5 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173171057/10000000000 : ℝ)*x 0 + (-1368800849/10000000000 : ℝ)*x 1 + (6004756511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173171057/10000000000 : ℝ)^4203 ≤ (8367273054027/20000000000000 : ℝ)^3179 := by
    have hnat : (5173171057 : ℕ)^4203*20000000000000^3179 ≤ 8367273054027^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173171057 10000000000 8367273054027 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368800849/10000000000 : ℝ)^4203 ≤ (3606728810137/50000000000000 : ℝ)^3179 := by
    have hnat : (1368800849 : ℕ)^4203*50000000000000^3179 ≤ 3606728810137^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368800849 10000000000 3606728810137 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6004756511/10000000000 : ℝ)^4203 ≤ (50950177091781/100000000000000 : ℝ)^3179 := by
    have hnat : (6004756511 : ℕ)^4203*100000000000000^3179 ≤ 50950177091781^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004756511 10000000000 50950177091781 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173171057/10000000000 : ℝ), (-1368800849/10000000000 : ℝ), (6004756511/10000000000 : ℝ)] ![(8367273054027/20000000000000 : ℝ), (3606728810137/50000000000000 : ℝ), (50950177091781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173171057/10000000000 : ℝ)|^4203 ≤ (8367273054027/20000000000000 : ℝ)^3179
        have hw : |(5173171057/10000000000 : ℝ)|=(5173171057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1368800849/10000000000 : ℝ)|^4203 ≤ (3606728810137/50000000000000 : ℝ)^3179
        have hw : |(-1368800849/10000000000 : ℝ)|=(1368800849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6004756511/10000000000 : ℝ)|^4203 ≤ (50950177091781/100000000000000 : ℝ)^3179
        have hw : |(6004756511/10000000000 : ℝ)|=(6004756511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s0_6 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (64664649/125000000 : ℝ)*x 0 + (300237763/500000000 : ℝ)*x 1 + (-1368801539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64664649/125000000 : ℝ)^4203 ≤ (41836374497481/100000000000000 : ℝ)^3179 := by
    have hnat : (64664649 : ℕ)^4203*100000000000000^3179 ≤ 41836374497481^3179*125000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64664649 125000000 41836374497481 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (300237763/500000000 : ℝ)^4203 ≤ (50950163057943/100000000000000 : ℝ)^3179 := by
    have hnat : (300237763 : ℕ)^4203*100000000000000^3179 ≤ 50950163057943^3179*500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300237763 500000000 50950163057943 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1368801539/10000000000 : ℝ)^4203 ≤ (1442692485559/20000000000000 : ℝ)^3179 := by
    have hnat : (1368801539 : ℕ)^4203*20000000000000^3179 ≤ 1442692485559^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368801539 10000000000 1442692485559 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(64664649/125000000 : ℝ), (300237763/500000000 : ℝ), (-1368801539/10000000000 : ℝ)] ![(41836374497481/100000000000000 : ℝ), (50950163057943/100000000000000 : ℝ), (1442692485559/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(64664649/125000000 : ℝ)|^4203 ≤ (41836374497481/100000000000000 : ℝ)^3179
        have hw : |(64664649/125000000 : ℝ)|=(64664649/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(300237763/500000000 : ℝ)|^4203 ≤ (50950163057943/100000000000000 : ℝ)^3179
        have hw : |(300237763/500000000 : ℝ)|=(300237763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1368801539/10000000000 : ℝ)|^4203 ≤ (1442692485559/20000000000000 : ℝ)^3179
        have hw : |(-1368801539/10000000000 : ℝ)|=(1368801539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s0_7 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (420527361/1000000000 : ℝ)*x 0 + (2785987313/5000000000 : ℝ)*x 1 + (199075309/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420527361/1000000000 : ℝ)^4203 ≤ (15906812933203/50000000000000 : ℝ)^3179 := by
    have hnat : (420527361 : ℕ)^4203*50000000000000^3179 ≤ 15906812933203^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420527361 1000000000 15906812933203 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2785987313/5000000000 : ℝ)^4203 ≤ (46152491118099/100000000000000 : ℝ)^3179 := by
    have hnat : (2785987313 : ℕ)^4203*100000000000000^3179 ≤ 46152491118099^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785987313 5000000000 46152491118099 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199075309/625000000 : ℝ)^4203 ≤ (22033883000463/100000000000000 : ℝ)^3179 := by
    have hnat : (199075309 : ℕ)^4203*100000000000000^3179 ≤ 22033883000463^3179*625000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199075309 625000000 22033883000463 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420527361/1000000000 : ℝ), (2785987313/5000000000 : ℝ), (199075309/625000000 : ℝ)] ![(15906812933203/50000000000000 : ℝ), (46152491118099/100000000000000 : ℝ), (22033883000463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420527361/1000000000 : ℝ)|^4203 ≤ (15906812933203/50000000000000 : ℝ)^3179
        have hw : |(420527361/1000000000 : ℝ)|=(420527361/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2785987313/5000000000 : ℝ)|^4203 ≤ (46152491118099/100000000000000 : ℝ)^3179
        have hw : |(2785987313/5000000000 : ℝ)|=(2785987313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(199075309/625000000 : ℝ)|^4203 ≤ (22033883000463/100000000000000 : ℝ)^3179
        have hw : |(199075309/625000000 : ℝ)|=(199075309/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1213_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (351/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5509/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8405/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8405 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8405*1^2048 ≤ 0^2048*1^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8405/2048 : ℝ) ≤ (465460300569684347/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8405 ≤ (465460300569684347/20000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8405*20000000000000000000^2048 ≤ 465460300569684347^2048*5^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 465460300569684347 20000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (465460300569684347/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8405 := by
      have hnat : (1 : ℕ)^2048*1^8405 ≤ 1^8405*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20465460300569684347/20000000000000000000 : ℝ) ≤ (2011243134336177/2000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (20465460300569684347/20000000000000000000 : ℝ)^2048 ≤ (2011243134336177/2000000000000000 : ℝ)^8405 := by
      have hnat : (20465460300569684347 : ℕ)^2048*2000000000000000^8405 ≤ 2011243134336177^8405*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20465460300569684347 20000000000000000000 2011243134336177 2000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011243134336177/2000000000000000 : ℝ)) (X := (20465460300569684347/20000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10465460300569684347/10000000000000000000 : ℝ) ≤ (1011243134336177/1000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (10465460300569684347/10000000000000000000 : ℝ)^2048 ≤ (1011243134336177/1000000000000000 : ℝ)^8405 := by
      have hnat : (10465460300569684347 : ℕ)^2048*1000000000000000^8405 ≤ 1011243134336177^8405*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10465460300569684347 10000000000000000000 1011243134336177 1000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011243134336177/1000000000000000 : ℝ)) (X := (10465460300569684347/10000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11243134336177/800000000000000 : ℝ)*(0 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11243134336177/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(465460300569684347/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11243134336177/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8405/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11243134336177/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011243134336177/2000000000000000 : ℝ) by norm_num, show 1+(465460300569684347/20000000000000000000 : ℝ)+(0 : ℝ)=(20465460300569684347/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(465460300569684347/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11243134336177/800000000000000 : ℝ)*(2/5 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11243134336177/800000000000000 : ℝ)*(2/5 : ℝ)=(1011243134336177/1000000000000000 : ℝ) by norm_num, show 1+2*(465460300569684347/20000000000000000000 : ℝ)=(10465460300569684347/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11243134336177/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11243134336177/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11243134336177/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11243134336177/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11243134336177/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11243134336177/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1869541277/10000000000 : ℝ)*X 0 0+(1207613063/2000000000 : ℝ)*X 0 1+(4789385711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5512793343/10000000000 : ℝ)*X 1 0+(-2584171569/10000000000 : ℝ)*X 1 1+(1197346421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2756396663/5000000000 : ℝ)*X 2 0+(598673213/1250000000 : ℝ)*X 2 1+(-2584171567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((839061749/2000000000 : ℝ)*X 0 0+(3118015143/10000000000 : ℝ)*X 0 1+(5636873457/10000000000 : ℝ)*X 0 2+(839061749/2000000000 : ℝ)*X 1 0+(3118015143/10000000000 : ℝ)*X 1 1+(5636873457/10000000000 : ℝ)*X 1 2+(839061749/2000000000 : ℝ)*X 2 0+(3118015143/10000000000 : ℝ)*X 2 1+(5636873457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-937240829/5000000000 : ℝ)*X 0 0+(602695013/1250000000 : ℝ)*X 0 1+(300237739/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173171057/10000000000 : ℝ)*X 1 0+(-1368800849/10000000000 : ℝ)*X 1 1+(6004756511/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((64664649/125000000 : ℝ)*X 2 0+(300237763/500000000 : ℝ)*X 2 1+(-1368801539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((420527361/1000000000 : ℝ)*X 0 0+(2785987313/5000000000 : ℝ)*X 0 1+(199075309/625000000 : ℝ)*X 0 2+(420527361/1000000000 : ℝ)*X 1 0+(2785987313/5000000000 : ℝ)*X 1 1+(199075309/625000000 : ℝ)*X 1 2+(420527361/1000000000 : ℝ)*X 2 0+(2785987313/5000000000 : ℝ)*X 2 1+(199075309/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119155735027715834898489/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2069867/3125000000000 : ℝ)*(base1) + (728343377/50000000000000 : ℝ)*(base19) + (338602549/25000000000000 : ℝ)*(base23) + (4990347/5000000000000 : ℝ)*(base24) + (332961697/100000000000000 : ℝ)*(upper3) + (299465897995581/50000000000000 : ℝ)*(major0) + (299465897995581/50000000000000 : ℝ)*(major1) + (299465897995581/50000000000000 : ℝ)*(major2) + (800850874344917/100000000000000 : ℝ)*(sp0) + (800852578231787/100000000000000 : ℝ)*(sp1) + (160170516140281/20000000000000 : ℝ)*(sp2) + (99251686889007/25000000000000 : ℝ)*(sp3) + (403351171/12500000000000 : ℝ)*(sp4) + (636169779/25000000000000 : ℝ)*(sp7) + (49626169808861/12500000000000 : ℝ)*(f.failure) + (800854034918541/100000000000000 : ℝ)*(f.sum) + (51109665093837/20000000000000000000000000000 : ℝ)*base65 + (198440715446163/40000000000000000000000000000 : ℝ)*base68 + (50086981353837/40000000000000000000000000000 : ℝ)*base69 + (50754188006163/40000000000000000000000000000 : ℝ)*base72 + (56749738093837/20000000000000000000000000000 : ℝ)*base73 + (33092109886163/40000000000000000000000000000 : ℝ)*base76 + (42683351566163/40000000000000000000000000000 : ℝ)*base78 + (68568955166163/40000000000000000000000000000 : ℝ)*base80 + (169534381133837/20000000000000000000000000000 : ℝ)*base81 + (494441/312500000000000000000 : ℝ)*base90 + (494441/312500000000000000000 : ℝ)*base92 + (494441/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74691417154131464527689/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26246923/2500000000000 : ℝ)*(base19) + (1275285867/100000000000000 : ℝ)*(base23) + (9050769/12500000000000 : ℝ)*(base39) + (129079243/50000000000000 : ℝ)*(upper3) + (1049449/3125000000000 : ℝ)*(upper5) + (316036186861257/50000000000000 : ℝ)*(major0) + (316036186861257/50000000000000 : ℝ)*(major1) + (316036150658181/50000000000000 : ℝ)*(major2) + (253084411/10000000000000 : ℝ)*(sp1) + (548751061/20000000000000 : ℝ)*(sp2) + (42258377485103/5000000000000 : ℝ)*(sp4) + (84516396898103/10000000000000 : ℝ)*(sp5) + (5282272519169/625000000000 : ℝ)*(sp6) + (52372125106389/12500000000000 : ℝ)*(sp7) + (52372125106389/12500000000000 : ℝ)*(f.failure) + (845167622108213/100000000000000 : ℝ)*(f.sum) + (54334294745737/20000000000000000000000000000 : ℝ)*base66 + (279820864765963/40000000000000000000000000000 : ℝ)*base68 + (68604113674489/40000000000000000000000000000 : ℝ)*base69 + (229383441085963/40000000000000000000000000000 : ℝ)*base72 + (140493138985737/20000000000000000000000000000 : ℝ)*base74 + (131129682874489/40000000000000000000000000000 : ℝ)*base75 + (135724727205511/40000000000000000000000000000 : ℝ)*base78 + (5782925514489/40000000000000000000000000000 : ℝ)*base79 + (124784309865511/20000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3184191/312500000000000000000 : ℝ)*base89 + (3184191/312500000000000000000 : ℝ)*base91 + (3184191/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1213_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (351/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5509/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1213_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1213_s1_0 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034531259/5000000000 : ℝ)*x 0 + (1136589369/2000000000 : ℝ)*x 1 + (2508393503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034531259/5000000000 : ℝ)^4203 ≤ (622794554723/5000000000000 : ℝ)^3179 := by
    have hnat : (1034531259 : ℕ)^4203*5000000000000^3179 ≤ 622794554723^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034531259 5000000000 622794554723 5000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136589369/2000000000 : ℝ)^4203 ≤ (47371631676871/100000000000000 : ℝ)^3179 := by
    have hnat : (1136589369 : ℕ)^4203*100000000000000^3179 ≤ 47371631676871^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136589369 2000000000 47371631676871 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508393503/5000000000 : ℝ)^4203 ≤ (20086238609277/50000000000000 : ℝ)^3179 := by
    have hnat : (2508393503 : ℕ)^4203*50000000000000^3179 ≤ 20086238609277^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508393503 5000000000 20086238609277 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034531259/5000000000 : ℝ), (1136589369/2000000000 : ℝ), (2508393503/5000000000 : ℝ)] ![(622794554723/5000000000000 : ℝ), (47371631676871/100000000000000 : ℝ), (20086238609277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034531259/5000000000 : ℝ)|^4203 ≤ (622794554723/5000000000000 : ℝ)^3179
        have hw : |(-1034531259/5000000000 : ℝ)|=(1034531259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1136589369/2000000000 : ℝ)|^4203 ≤ (47371631676871/100000000000000 : ℝ)^3179
        have hw : |(1136589369/2000000000 : ℝ)|=(1136589369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2508393503/5000000000 : ℝ)|^4203 ≤ (20086238609277/50000000000000 : ℝ)^3179
        have hw : |(2508393503/5000000000 : ℝ)|=(2508393503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s1_1 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5415235843/10000000000 : ℝ)*x 0 + (-1213641999/5000000000 : ℝ)*x 1 + (15677461/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5415235843/10000000000 : ℝ)^4203 ≤ (11110966692193/25000000000000 : ℝ)^3179 := by
    have hnat : (5415235843 : ℕ)^4203*25000000000000^3179 ≤ 11110966692193^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415235843 10000000000 11110966692193 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213641999/5000000000 : ℝ)^4203 ≤ (15383650546331/100000000000000 : ℝ)^3179 := by
    have hnat : (1213641999 : ℕ)^4203*100000000000000^3179 ≤ 15383650546331^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213641999 5000000000 15383650546331 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15677461/31250000 : ℝ)^4203 ≤ (40172482660259/100000000000000 : ℝ)^3179 := by
    have hnat : (15677461 : ℕ)^4203*100000000000000^3179 ≤ 40172482660259^3179*31250000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15677461 31250000 40172482660259 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5415235843/10000000000 : ℝ), (-1213641999/5000000000 : ℝ), (15677461/31250000 : ℝ)] ![(11110966692193/25000000000000 : ℝ), (15383650546331/100000000000000 : ℝ), (40172482660259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5415235843/10000000000 : ℝ)|^4203 ≤ (11110966692193/25000000000000 : ℝ)^3179
        have hw : |(5415235843/10000000000 : ℝ)|=(5415235843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1213641999/5000000000 : ℝ)|^4203 ≤ (15383650546331/100000000000000 : ℝ)^3179
        have hw : |(-1213641999/5000000000 : ℝ)|=(1213641999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15677461/31250000 : ℝ)|^4203 ≤ (40172482660259/100000000000000 : ℝ)^3179
        have hw : |(15677461/31250000 : ℝ)|=(15677461/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s1_2 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (541523451/1000000000 : ℝ)*x 0 + (5016788373/10000000000 : ℝ)*x 1 + (-2427284647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541523451/1000000000 : ℝ)^4203 ≤ (11110963076151/25000000000000 : ℝ)^3179 := by
    have hnat : (541523451 : ℕ)^4203*25000000000000^3179 ≤ 11110963076151^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541523451 1000000000 11110963076151 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5016788373/10000000000 : ℝ)^4203 ≤ (40172491690947/100000000000000 : ℝ)^3179 := by
    have hnat : (5016788373 : ℕ)^4203*100000000000000^3179 ≤ 40172491690947^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5016788373 10000000000 40172491690947 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2427284647/10000000000 : ℝ)^4203 ≤ (961478499031/6250000000000 : ℝ)^3179 := by
    have hnat : (2427284647 : ℕ)^4203*6250000000000^3179 ≤ 961478499031^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2427284647 10000000000 961478499031 6250000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541523451/1000000000 : ℝ), (5016788373/10000000000 : ℝ), (-2427284647/10000000000 : ℝ)] ![(11110963076151/25000000000000 : ℝ), (40172491690947/100000000000000 : ℝ), (961478499031/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541523451/1000000000 : ℝ)|^4203 ≤ (11110963076151/25000000000000 : ℝ)^3179
        have hw : |(541523451/1000000000 : ℝ)|=(541523451/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5016788373/10000000000 : ℝ)|^4203 ≤ (40172491690947/100000000000000 : ℝ)^3179
        have hw : |(5016788373/10000000000 : ℝ)|=(5016788373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2427284647/10000000000 : ℝ)|^4203 ≤ (961478499031/6250000000000 : ℝ)^3179
        have hw : |(-2427284647/10000000000 : ℝ)|=(2427284647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s1_3 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (862273143/2000000000 : ℝ)*x 0 + (147607597/400000000 : ℝ)*x 1 + (5033980461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862273143/2000000000 : ℝ)^4203 ≤ (32879048640837/100000000000000 : ℝ)^3179 := by
    have hnat : (862273143 : ℕ)^4203*100000000000000^3179 ≤ 32879048640837^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862273143 2000000000 32879048640837 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (147607597/400000000 : ℝ)^4203 ≤ (6691586768989/25000000000000 : ℝ)^3179 := by
    have hnat : (147607597 : ℕ)^4203*25000000000000^3179 ≤ 6691586768989^3179*400000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147607597 400000000 6691586768989 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5033980461/10000000000 : ℝ)^4203 ≤ (40354604261167/100000000000000 : ℝ)^3179 := by
    have hnat : (5033980461 : ℕ)^4203*100000000000000^3179 ≤ 40354604261167^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033980461 10000000000 40354604261167 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862273143/2000000000 : ℝ), (147607597/400000000 : ℝ), (5033980461/10000000000 : ℝ)] ![(32879048640837/100000000000000 : ℝ), (6691586768989/25000000000000 : ℝ), (40354604261167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862273143/2000000000 : ℝ)|^4203 ≤ (32879048640837/100000000000000 : ℝ)^3179
        have hw : |(862273143/2000000000 : ℝ)|=(862273143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(147607597/400000000 : ℝ)|^4203 ≤ (6691586768989/25000000000000 : ℝ)^3179
        have hw : |(147607597/400000000 : ℝ)|=(147607597/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5033980461/10000000000 : ℝ)|^4203 ≤ (40354604261167/100000000000000 : ℝ)^3179
        have hw : |(5033980461/10000000000 : ℝ)|=(5033980461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s1_4 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-206977119/1000000000 : ℝ)*x 0 + (628204497/1250000000 : ℝ)*x 1 + (5673929669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206977119/1000000000 : ℝ)^4203 ≤ (12461531875991/100000000000000 : ℝ)^3179 := by
    have hnat : (206977119 : ℕ)^4203*100000000000000^3179 ≤ 12461531875991^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206977119 1000000000 12461531875991 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628204497/1250000000 : ℝ)^4203 ≤ (805323752599/2000000000000 : ℝ)^3179 := by
    have hnat : (628204497 : ℕ)^4203*2000000000000^3179 ≤ 805323752599^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628204497 1250000000 805323752599 2000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673929669/10000000000 : ℝ)^4203 ≤ (23636140238049/50000000000000 : ℝ)^3179 := by
    have hnat : (5673929669 : ℕ)^4203*50000000000000^3179 ≤ 23636140238049^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673929669 10000000000 23636140238049 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-206977119/1000000000 : ℝ), (628204497/1250000000 : ℝ), (5673929669/10000000000 : ℝ)] ![(12461531875991/100000000000000 : ℝ), (805323752599/2000000000000 : ℝ), (23636140238049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-206977119/1000000000 : ℝ)|^4203 ≤ (12461531875991/100000000000000 : ℝ)^3179
        have hw : |(-206977119/1000000000 : ℝ)|=(206977119/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(628204497/1250000000 : ℝ)|^4203 ≤ (805323752599/2000000000000 : ℝ)^3179
        have hw : |(628204497/1250000000 : ℝ)|=(628204497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673929669/10000000000 : ℝ)|^4203 ≤ (23636140238049/50000000000000 : ℝ)^3179
        have hw : |(5673929669/10000000000 : ℝ)|=(5673929669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s1_5 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048769939/2000000000 : ℝ)*x 0 + (-885072861/5000000000 : ℝ)*x 1 + (113478513/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048769939/2000000000 : ℝ)^4203 ≤ (42593731272029/100000000000000 : ℝ)^3179 := by
    have hnat : (1048769939 : ℕ)^4203*100000000000000^3179 ≤ 42593731272029^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048769939 2000000000 42593731272029 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (885072861/5000000000 : ℝ)^4203 ≤ (5067016256407/50000000000000 : ℝ)^3179 := by
    have hnat : (885072861 : ℕ)^4203*50000000000000^3179 ≤ 5067016256407^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      885072861 5000000000 5067016256407 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113478513/200000000 : ℝ)^4203 ≤ (11818059051527/25000000000000 : ℝ)^3179 := by
    have hnat : (113478513 : ℕ)^4203*25000000000000^3179 ≤ 11818059051527^3179*200000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113478513 200000000 11818059051527 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048769939/2000000000 : ℝ), (-885072861/5000000000 : ℝ), (113478513/200000000 : ℝ)] ![(42593731272029/100000000000000 : ℝ), (5067016256407/50000000000000 : ℝ), (11818059051527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048769939/2000000000 : ℝ)|^4203 ≤ (42593731272029/100000000000000 : ℝ)^3179
        have hw : |(1048769939/2000000000 : ℝ)|=(1048769939/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-885072861/5000000000 : ℝ)|^4203 ≤ (5067016256407/50000000000000 : ℝ)^3179
        have hw : |(-885072861/5000000000 : ℝ)|=(885072861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(113478513/200000000 : ℝ)|^4203 ≤ (11818059051527/25000000000000 : ℝ)^3179
        have hw : |(113478513/200000000 : ℝ)|=(113478513/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s1_6 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1310962463/2500000000 : ℝ)*x 0 + (5673926089/10000000000 : ℝ)*x 1 + (-1770144859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1310962463/2500000000 : ℝ)^4203 ≤ (21296866479027/50000000000000 : ℝ)^3179 := by
    have hnat : (1310962463 : ℕ)^4203*50000000000000^3179 ≤ 21296866479027^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310962463 2500000000 21296866479027 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5673926089/10000000000 : ℝ)^4203 ≤ (4727224104177/10000000000000 : ℝ)^3179 := by
    have hnat : (5673926089 : ℕ)^4203*10000000000000^3179 ≤ 4727224104177^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673926089 10000000000 4727224104177 10000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1770144859/10000000000 : ℝ)^4203 ≤ (10134025980713/100000000000000 : ℝ)^3179 := by
    have hnat : (1770144859 : ℕ)^4203*100000000000000^3179 ≤ 10134025980713^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1770144859 10000000000 10134025980713 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1310962463/2500000000 : ℝ), (5673926089/10000000000 : ℝ), (-1770144859/10000000000 : ℝ)] ![(21296866479027/50000000000000 : ℝ), (4727224104177/10000000000000 : ℝ), (10134025980713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1310962463/2500000000 : ℝ)|^4203 ≤ (21296866479027/50000000000000 : ℝ)^3179
        have hw : |(1310962463/2500000000 : ℝ)|=(1310962463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5673926089/10000000000 : ℝ)|^4203 ≤ (4727224104177/10000000000000 : ℝ)^3179
        have hw : |(5673926089/10000000000 : ℝ)|=(5673926089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1770144859/10000000000 : ℝ)|^4203 ≤ (10134025980713/100000000000000 : ℝ)^3179
        have hw : |(-1770144859/10000000000 : ℝ)|=(1770144859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s1_7 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312800729/10000000000 : ℝ)*x 0 + (156753951/312500000 : ℝ)*x 1 + (1854193827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312800729/10000000000 : ℝ)^4203 ≤ (1315740724479/4000000000000 : ℝ)^3179 := by
    have hnat : (4312800729 : ℕ)^4203*4000000000000^3179 ≤ 1315740724479^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312800729 10000000000 1315740724479 4000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (156753951/312500000 : ℝ)^4203 ≤ (5020685485957/12500000000000 : ℝ)^3179 := by
    have hnat : (156753951 : ℕ)^4203*12500000000000^3179 ≤ 5020685485957^3179*312500000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      156753951 312500000 5020685485957 12500000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1854193827/5000000000 : ℝ)^4203 ≤ (26940997985811/100000000000000 : ℝ)^3179 := by
    have hnat : (1854193827 : ℕ)^4203*100000000000000^3179 ≤ 26940997985811^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1854193827 5000000000 26940997985811 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312800729/10000000000 : ℝ), (156753951/312500000 : ℝ), (1854193827/5000000000 : ℝ)] ![(1315740724479/4000000000000 : ℝ), (5020685485957/12500000000000 : ℝ), (26940997985811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312800729/10000000000 : ℝ)|^4203 ≤ (1315740724479/4000000000000 : ℝ)^3179
        have hw : |(4312800729/10000000000 : ℝ)|=(4312800729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(156753951/312500000 : ℝ)|^4203 ≤ (5020685485957/12500000000000 : ℝ)^3179
        have hw : |(156753951/312500000 : ℝ)|=(156753951/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1854193827/5000000000 : ℝ)|^4203 ≤ (26940997985811/100000000000000 : ℝ)^3179
        have hw : |(1854193827/5000000000 : ℝ)|=(1854193827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1213_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5509/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3019/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20123/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5509/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (351/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5509/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (351/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5509/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (351/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5509/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (351/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5509/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (351/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5509/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (351/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (351/50000 : ℝ) ^ (8405/2048 : ℝ) ≤ (5799881051/4000000000000000000 : ℝ) := by
    have hpowers : (351/50000 : ℝ)^8405 ≤ (5799881051/4000000000000000000 : ℝ)^2048 := by
      have hnat : (351 : ℕ)^8405*4000000000000000000^2048 ≤ 5799881051^2048*50000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        351 50000 5799881051 4000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (351/50000 : ℝ)) (X := (5799881051/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5509/20000 : ℝ) ^ (8405/2048 : ℝ) ≤ (251711682515995821/50000000000000000000 : ℝ) := by
    have hpowers : (5509/20000 : ℝ)^8405 ≤ (251711682515995821/50000000000000000000 : ℝ)^2048 := by
      have hnat : (5509 : ℕ)^8405*50000000000000000000^2048 ≤ 251711682515995821^2048*20000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5509 20000 251711682515995821 50000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5509/20000 : ℝ)) (X := (251711682515995821/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000000005799881051/2000000000000000000 : ℝ) ≤ (5000000003533063/5000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (2000000005799881051/2000000000000000000 : ℝ)^2048 ≤ (5000000003533063/5000000000000000 : ℝ)^8405 := by
      have hnat : (2000000005799881051 : ℕ)^2048*5000000000000000^8405 ≤ 5000000003533063^8405*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000000005799881051 2000000000000000000 5000000003533063 5000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000003533063/5000000000000000 : ℝ)) (X := (2000000005799881051/2000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100503423510029017917/100000000000000000000 : ℝ) ≤ (10012243358586169/10000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (100503423510029017917/100000000000000000000 : ℝ)^2048 ≤ (10012243358586169/10000000000000000 : ℝ)^8405 := by
      have hnat : (100503423510029017917 : ℕ)^2048*10000000000000000^8405 ≤ 10012243358586169^8405*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100503423510029017917 100000000000000000000 10012243358586169 10000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10012243358586169/10000000000000000 : ℝ)) (X := (100503423510029017917/100000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25251711682515995821/25000000000000000000 : ℝ) ≤ (2506121677526553/2500000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (25251711682515995821/25000000000000000000 : ℝ)^2048 ≤ (2506121677526553/2500000000000000 : ℝ)^8405 := by
      have hnat : (25251711682515995821 : ℕ)^2048*2500000000000000^8405 ≤ 2506121677526553^8405*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25251711682515995821 25000000000000000000 2506121677526553 2500000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506121677526553/2500000000000000 : ℝ)) (X := (25251711682515995821/25000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5799881051/4000000000000000000 : ℝ) ≤ ((134206405262070939923/134215000000000000000 : ℝ)+2*(12243351520043/2684300000000000 : ℝ)*(351/50000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (134206405262070939923/134215000000000000000 : ℝ)+2*(12243351520043/2684300000000000 : ℝ)*(351/50000 : ℝ)=(5000000003533063/5000000000000000 : ℝ) by norm_num, show 1+2*(5799881051/4000000000000000000 : ℝ)=(2000000005799881051/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(251711682515995821/50000000000000000000 : ℝ)+(5799881051/4000000000000000000 : ℝ) ≤ ((134206405262070939923/134215000000000000000 : ℝ)+(12243351520043/2684300000000000 : ℝ)*((5509/20000 : ℝ)+(351/50000 : ℝ)))^(8405/2048 : ℝ) := by
    rw [show (134206405262070939923/134215000000000000000 : ℝ)+(12243351520043/2684300000000000 : ℝ)*((5509/20000 : ℝ)+(351/50000 : ℝ))=(10012243358586169/10000000000000000 : ℝ) by norm_num, show 1+(251711682515995821/50000000000000000000 : ℝ)+(5799881051/4000000000000000000 : ℝ)=(100503423510029017917/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(251711682515995821/50000000000000000000 : ℝ) ≤ ((134206405262070939923/134215000000000000000 : ℝ)+2*(12243351520043/2684300000000000 : ℝ)*(5509/20000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (134206405262070939923/134215000000000000000 : ℝ)+2*(12243351520043/2684300000000000 : ℝ)*(5509/20000 : ℝ)=(2506121677526553/2500000000000000 : ℝ) by norm_num, show 1+2*(251711682515995821/50000000000000000000 : ℝ)=(25251711682515995821/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (134206405262070939923/134215000000000000000 : ℝ)*(X 1 0+X 2 0)+(12243351520043/2684300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (351/50000 : ℝ)) (hi := (5509/20000 : ℝ)) (c := (134206405262070939923/134215000000000000000 : ℝ)) (alpha := (12243351520043/2684300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (134206405262070939923/134215000000000000000 : ℝ)*(X 0 1+X 2 1)+(12243351520043/2684300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (351/50000 : ℝ)) (hi := (5509/20000 : ℝ)) (c := (134206405262070939923/134215000000000000000 : ℝ)) (alpha := (12243351520043/2684300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (134206405262070939923/134215000000000000000 : ℝ)*(X 0 2+X 1 2)+(12243351520043/2684300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (351/50000 : ℝ)) (hi := (5509/20000 : ℝ)) (c := (134206405262070939923/134215000000000000000 : ℝ)) (alpha := (12243351520043/2684300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1034531259/5000000000 : ℝ)*X 0 0+(1136589369/2000000000 : ℝ)*X 0 1+(2508393503/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5415235843/10000000000 : ℝ)*X 1 0+(-1213641999/5000000000 : ℝ)*X 1 1+(15677461/31250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((541523451/1000000000 : ℝ)*X 2 0+(5016788373/10000000000 : ℝ)*X 2 1+(-2427284647/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862273143/2000000000 : ℝ)*X 0 0+(147607597/400000000 : ℝ)*X 0 1+(5033980461/10000000000 : ℝ)*X 0 2+(862273143/2000000000 : ℝ)*X 1 0+(147607597/400000000 : ℝ)*X 1 1+(5033980461/10000000000 : ℝ)*X 1 2+(862273143/2000000000 : ℝ)*X 2 0+(147607597/400000000 : ℝ)*X 2 1+(5033980461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-206977119/1000000000 : ℝ)*X 0 0+(628204497/1250000000 : ℝ)*X 0 1+(5673929669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1048769939/2000000000 : ℝ)*X 1 0+(-885072861/5000000000 : ℝ)*X 1 1+(113478513/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1310962463/2500000000 : ℝ)*X 2 0+(5673926089/10000000000 : ℝ)*X 2 1+(-1770144859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312800729/10000000000 : ℝ)*X 0 0+(156753951/312500000 : ℝ)*X 0 1+(1854193827/5000000000 : ℝ)*X 0 2+(4312800729/10000000000 : ℝ)*X 1 0+(156753951/312500000 : ℝ)*X 1 1+(1854193827/5000000000 : ℝ)*X 1 2+(4312800729/10000000000 : ℝ)*X 2 0+(156753951/312500000 : ℝ)*X 2 1+(1854193827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1188126693035612158209159081/419421875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (792757699/100000000000000 : ℝ)*(base19) + (578210243/100000000000000 : ℝ)*(base23) + (93520049/100000000000000 : ℝ)*(upper2) + (209071659/100000000000000 : ℝ)*(upper3) + (9598993/100000000000000 : ℝ)*(upper4) + (274087236457/24414062500 : ℝ)*(major0) + (274087236457/24414062500 : ℝ)*(major1) + (274087236457/24414062500 : ℝ)*(major2) + (750574291214669/50000000000000 : ℝ)*(sp0) + (750575896955031/50000000000000 : ℝ)*(sp1) + (750576004228759/50000000000000 : ℝ)*(sp2) + (744166510981287/100000000000000 : ℝ)*(sp3) + (500529803/12500000000000 : ℝ)*(sp4) + (215561309/6250000000000 : ℝ)*(sp7) + (93021244995279/12500000000000 : ℝ)*(f.failure) + (1501152586667761/100000000000000 : ℝ)*(f.sum) + (291890227347041/134215000000000000000000000000 : ℝ)*base65 + (810786777680260433/419421875000000000000000000000000 : ℝ)*base67 + (191780214306041683/419421875000000000000000000000000 : ℝ)*base69 + (2847788833133541683/419421875000000000000000000000000 : ℝ)*base71 + (341988436257991/134215000000000000000000000000 : ℝ)*base73 + (3308486318513729183/419421875000000000000000000000000 : ℝ)*base75 + (129182676360072933/419421875000000000000000000000000 : ℝ)*base77 + (2904390716921822933/419421875000000000000000000000000 : ℝ)*base79 + (577869268085041/134215000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1451101/312500000000000000000 : ℝ)*base89 + (1451101/312500000000000000000 : ℝ)*base91 + (1451101/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (233781664033608503630811/26843000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21922489/2500000000000 : ℝ)*(base19) + (1780131877/100000000000000 : ℝ)*(base23) + (2564333/50000000000000 : ℝ)*(lower3) + (88104533/25000000000000 : ℝ)*(lower4) + (230720005710963/20000000000000 : ℝ)*(major0) + (230720005710963/20000000000000 : ℝ)*(major1) + (230720005710963/20000000000000 : ℝ)*(major2) + (6013109947/100000000000000 : ℝ)*(sp0) + (2430076189/100000000000000 : ℝ)*(sp1) + (4045108169/50000000000000 : ℝ)*(sp2) + (61700627518101/4000000000000 : ℝ)*(sp4) + (1542518394086723/100000000000000 : ℝ)*(sp5) + (771255915357129/50000000000000 : ℝ)*(sp6) + (191169516434933/25000000000000 : ℝ)*(sp7) + (191169516434933/25000000000000 : ℝ)*(f.failure) + (192815212632809/12500000000000 : ℝ)*(f.sum) + (44500771029467/26843000000000000000000000000 : ℝ)*base66 + (5940922307118225849/2684300000000000000000000000000000 : ℝ)*base67 + (3667741054984574151/2684300000000000000000000000000000 : ℝ)*base70 + (2822292900953925849/2684300000000000000000000000000000 : ℝ)*base71 + (77017851456019/26843000000000000000000000000 : ℝ)*base74 + (738286888086525849/2684300000000000000000000000000000 : ℝ)*base75 + (12398419259417274151/2684300000000000000000000000000000 : ℝ)*base78 + (15913865607372074151/2684300000000000000000000000000000 : ℝ)*base80 + (57464949200651/26843000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3595327/625000000000000000000 : ℝ)*base89 + (3595327/625000000000000000000 : ℝ)*base91 + (3595327/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1213_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5509/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (351/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3019/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20123/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1213_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1213_s2_0 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-529642431/2500000000 : ℝ)*x 0 + (1099562507/2000000000 : ℝ)*x 1 + (5170375189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529642431/2500000000 : ℝ)^4203 ≤ (1285143978711/10000000000000 : ℝ)^3179 := by
    have hnat : (529642431 : ℕ)^4203*10000000000000^3179 ≤ 1285143978711^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529642431 2500000000 1285143978711 10000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099562507/2000000000 : ℝ)^4203 ≤ (22671043114159/50000000000000 : ℝ)^3179 := by
    have hnat : (1099562507 : ℕ)^4203*50000000000000^3179 ≤ 22671043114159^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099562507 2000000000 22671043114159 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170375189/10000000000 : ℝ)^4203 ≤ (8361294793749/20000000000000 : ℝ)^3179 := by
    have hnat : (5170375189 : ℕ)^4203*20000000000000^3179 ≤ 8361294793749^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170375189 10000000000 8361294793749 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529642431/2500000000 : ℝ), (1099562507/2000000000 : ℝ), (5170375189/10000000000 : ℝ)] ![(1285143978711/10000000000000 : ℝ), (22671043114159/50000000000000 : ℝ), (8361294793749/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529642431/2500000000 : ℝ)|^4203 ≤ (1285143978711/10000000000000 : ℝ)^3179
        have hw : |(-529642431/2500000000 : ℝ)|=(529642431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099562507/2000000000 : ℝ)|^4203 ≤ (22671043114159/50000000000000 : ℝ)^3179
        have hw : |(1099562507/2000000000 : ℝ)|=(1099562507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170375189/10000000000 : ℝ)|^4203 ≤ (8361294793749/20000000000000 : ℝ)^3179
        have hw : |(5170375189/10000000000 : ℝ)|=(5170375189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_1 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537087231/1000000000 : ℝ)*x 0 + (-457669933/2000000000 : ℝ)*x 1 + (5170380039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537087231/1000000000 : ℝ)^4203 ≤ (43963121542279/100000000000000 : ℝ)^3179 := by
    have hnat : (537087231 : ℕ)^4203*100000000000000^3179 ≤ 43963121542279^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537087231 1000000000 43963121542279 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457669933/2000000000 : ℝ)^4203 ≤ (7115176315633/50000000000000 : ℝ)^3179 := by
    have hnat : (457669933 : ℕ)^4203*50000000000000^3179 ≤ 7115176315633^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457669933 2000000000 7115176315633 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170380039/10000000000 : ℝ)^4203 ≤ (20903262908381/50000000000000 : ℝ)^3179 := by
    have hnat : (5170380039 : ℕ)^4203*50000000000000^3179 ≤ 20903262908381^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170380039 10000000000 20903262908381 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537087231/1000000000 : ℝ), (-457669933/2000000000 : ℝ), (5170380039/10000000000 : ℝ)] ![(43963121542279/100000000000000 : ℝ), (7115176315633/50000000000000 : ℝ), (20903262908381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537087231/1000000000 : ℝ)|^4203 ≤ (43963121542279/100000000000000 : ℝ)^3179
        have hw : |(537087231/1000000000 : ℝ)|=(537087231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-457669933/2000000000 : ℝ)|^4203 ≤ (7115176315633/50000000000000 : ℝ)^3179
        have hw : |(-457669933/2000000000 : ℝ)|=(457669933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170380039/10000000000 : ℝ)|^4203 ≤ (20903262908381/50000000000000 : ℝ)^3179
        have hw : |(5170380039/10000000000 : ℝ)|=(5170380039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_2 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5370874559/10000000000 : ℝ)*x 0 + (2585188467/5000000000 : ℝ)*x 1 + (-1144175371/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370874559/10000000000 : ℝ)^4203 ≤ (1099078647031/2500000000000 : ℝ)^3179 := by
    have hnat : (5370874559 : ℕ)^4203*2500000000000^3179 ≤ 1099078647031^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370874559 10000000000 1099078647031 2500000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585188467/5000000000 : ℝ)^4203 ≤ (41806492623339/100000000000000 : ℝ)^3179 := by
    have hnat : (2585188467 : ℕ)^4203*100000000000000^3179 ≤ 41806492623339^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585188467 5000000000 41806492623339 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1144175371/5000000000 : ℝ)^4203 ≤ (444698796439/3125000000000 : ℝ)^3179 := by
    have hnat : (1144175371 : ℕ)^4203*3125000000000^3179 ≤ 444698796439^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144175371 5000000000 444698796439 3125000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370874559/10000000000 : ℝ), (2585188467/5000000000 : ℝ), (-1144175371/5000000000 : ℝ)] ![(1099078647031/2500000000000 : ℝ), (41806492623339/100000000000000 : ℝ), (444698796439/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370874559/10000000000 : ℝ)|^4203 ≤ (1099078647031/2500000000000 : ℝ)^3179
        have hw : |(5370874559/10000000000 : ℝ)|=(5370874559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585188467/5000000000 : ℝ)|^4203 ≤ (41806492623339/100000000000000 : ℝ)^3179
        have hw : |(2585188467/5000000000 : ℝ)|=(2585188467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1144175371/5000000000 : ℝ)|^4203 ≤ (444698796439/3125000000000 : ℝ)^3179
        have hw : |(-1144175371/5000000000 : ℝ)|=(1144175371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_3 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4345498999/10000000000 : ℝ)*x 0 + (805495911/2000000000 : ℝ)*x 1 + (4687989269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345498999/10000000000 : ℝ)^4203 ≤ (33223639492299/100000000000000 : ℝ)^3179 := by
    have hnat : (4345498999 : ℕ)^4203*100000000000000^3179 ≤ 33223639492299^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345498999 10000000000 33223639492299 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (805495911/2000000000 : ℝ)^4203 ≤ (15023776352139/50000000000000 : ℝ)^3179 := by
    have hnat : (805495911 : ℕ)^4203*50000000000000^3179 ≤ 15023776352139^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805495911 2000000000 15023776352139 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4687989269/10000000000 : ℝ)^4203 ≤ (7345761557839/20000000000000 : ℝ)^3179 := by
    have hnat : (4687989269 : ℕ)^4203*20000000000000^3179 ≤ 7345761557839^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4687989269 10000000000 7345761557839 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345498999/10000000000 : ℝ), (805495911/2000000000 : ℝ), (4687989269/10000000000 : ℝ)] ![(33223639492299/100000000000000 : ℝ), (15023776352139/50000000000000 : ℝ), (7345761557839/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345498999/10000000000 : ℝ)|^4203 ≤ (33223639492299/100000000000000 : ℝ)^3179
        have hw : |(4345498999/10000000000 : ℝ)|=(4345498999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(805495911/2000000000 : ℝ)|^4203 ≤ (15023776352139/50000000000000 : ℝ)^3179
        have hw : |(805495911/2000000000 : ℝ)|=(805495911/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4687989269/10000000000 : ℝ)|^4203 ≤ (7345761557839/20000000000000 : ℝ)^3179
        have hw : |(4687989269/10000000000 : ℝ)|=(4687989269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_4 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-132415813/625000000 : ℝ)*x 0 + (2586262421/5000000000 : ℝ)*x 1 + (5495643447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132415813/625000000 : ℝ)^4203 ≤ (1285210773443/10000000000000 : ℝ)^3179 := by
    have hnat : (132415813 : ℕ)^4203*10000000000000^3179 ≤ 1285210773443^3179*625000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132415813 625000000 1285210773443 10000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586262421/5000000000 : ℝ)^4203 ≤ (41829455966699/100000000000000 : ℝ)^3179 := by
    have hnat : (2586262421 : ℕ)^4203*100000000000000^3179 ≤ 41829455966699^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586262421 5000000000 41829455966699 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495643447/10000000000 : ℝ)^4203 ≤ (45318436290373/100000000000000 : ℝ)^3179 := by
    have hnat : (5495643447 : ℕ)^4203*100000000000000^3179 ≤ 45318436290373^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495643447 10000000000 45318436290373 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-132415813/625000000 : ℝ), (2586262421/5000000000 : ℝ), (5495643447/10000000000 : ℝ)] ![(1285210773443/10000000000000 : ℝ), (41829455966699/100000000000000 : ℝ), (45318436290373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-132415813/625000000 : ℝ)|^4203 ≤ (1285210773443/10000000000000 : ℝ)^3179
        have hw : |(-132415813/625000000 : ℝ)|=(132415813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586262421/5000000000 : ℝ)|^4203 ≤ (41829455966699/100000000000000 : ℝ)^3179
        have hw : |(2586262421/5000000000 : ℝ)|=(2586262421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495643447/10000000000 : ℝ)|^4203 ≤ (45318436290373/100000000000000 : ℝ)^3179
        have hw : |(5495643447/10000000000 : ℝ)|=(5495643447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_5 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211496333/400000000 : ℝ)*x 0 + (-392616913/2000000000 : ℝ)*x 1 + (5495643477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211496333/400000000 : ℝ)^4203 ≤ (43062132545871/100000000000000 : ℝ)^3179 := by
    have hnat : (211496333 : ℕ)^4203*100000000000000^3179 ≤ 43062132545871^3179*400000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211496333 400000000 43062132545871 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (392616913/2000000000 : ℝ)^4203 ≤ (2323886163137/20000000000000 : ℝ)^3179 := by
    have hnat : (392616913 : ℕ)^4203*20000000000000^3179 ≤ 2323886163137^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392616913 2000000000 2323886163137 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495643477/10000000000 : ℝ)^4203 ≤ (45318436617447/100000000000000 : ℝ)^3179 := by
    have hnat : (5495643477 : ℕ)^4203*100000000000000^3179 ≤ 45318436617447^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495643477 10000000000 45318436617447 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211496333/400000000 : ℝ), (-392616913/2000000000 : ℝ), (5495643477/10000000000 : ℝ)] ![(43062132545871/100000000000000 : ℝ), (2323886163137/20000000000000 : ℝ), (45318436617447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211496333/400000000 : ℝ)|^4203 ≤ (43062132545871/100000000000000 : ℝ)^3179
        have hw : |(211496333/400000000 : ℝ)|=(211496333/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-392616913/2000000000 : ℝ)|^4203 ≤ (2323886163137/20000000000000 : ℝ)^3179
        have hw : |(-392616913/2000000000 : ℝ)|=(392616913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495643477/10000000000 : ℝ)|^4203 ≤ (45318436617447/100000000000000 : ℝ)^3179
        have hw : |(5495643477/10000000000 : ℝ)|=(5495643477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_6 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643704253/5000000000 : ℝ)*x 0 + (686955439/1250000000 : ℝ)*x 1 + (-490771067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643704253/5000000000 : ℝ)^4203 ≤ (21531067247409/50000000000000 : ℝ)^3179 := by
    have hnat : (2643704253 : ℕ)^4203*50000000000000^3179 ≤ 21531067247409^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643704253 5000000000 21531067247409 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (686955439/1250000000 : ℝ)^4203 ≤ (22659218499517/50000000000000 : ℝ)^3179 := by
    have hnat : (686955439 : ℕ)^4203*50000000000000^3179 ≤ 22659218499517^3179*1250000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686955439 1250000000 22659218499517 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (490771067/2500000000 : ℝ)^4203 ≤ (11619428491497/100000000000000 : ℝ)^3179 := by
    have hnat : (490771067 : ℕ)^4203*100000000000000^3179 ≤ 11619428491497^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490771067 2500000000 11619428491497 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643704253/5000000000 : ℝ), (686955439/1250000000 : ℝ), (-490771067/2500000000 : ℝ)] ![(21531067247409/50000000000000 : ℝ), (22659218499517/50000000000000 : ℝ), (11619428491497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643704253/5000000000 : ℝ)|^4203 ≤ (21531067247409/50000000000000 : ℝ)^3179
        have hw : |(2643704253/5000000000 : ℝ)|=(2643704253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(686955439/1250000000 : ℝ)|^4203 ≤ (22659218499517/50000000000000 : ℝ)^3179
        have hw : |(686955439/1250000000 : ℝ)|=(686955439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-490771067/2500000000 : ℝ)|^4203 ≤ (11619428491497/100000000000000 : ℝ)^3179
        have hw : |(-490771067/2500000000 : ℝ)|=(490771067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_7 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434566949/1000000000 : ℝ)*x 0 + (4683655557/10000000000 : ℝ)*x 1 + (403185437/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434566949/1000000000 : ℝ)^4203 ≤ (33225362870581/100000000000000 : ℝ)^3179 := by
    have hnat : (434566949 : ℕ)^4203*100000000000000^3179 ≤ 33225362870581^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434566949 1000000000 33225362870581 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4683655557/10000000000 : ℝ)^4203 ≤ (36683924523073/100000000000000 : ℝ)^3179 := by
    have hnat : (4683655557 : ℕ)^4203*100000000000000^3179 ≤ 36683924523073^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4683655557 10000000000 36683924523073 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403185437/1000000000 : ℝ)^4203 ≤ (3673182689/12207031250 : ℝ)^3179 := by
    have hnat : (403185437 : ℕ)^4203*12207031250^3179 ≤ 3673182689^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403185437 1000000000 3673182689 12207031250 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434566949/1000000000 : ℝ), (4683655557/10000000000 : ℝ), (403185437/1000000000 : ℝ)] ![(33225362870581/100000000000000 : ℝ), (36683924523073/100000000000000 : ℝ), (3673182689/12207031250 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434566949/1000000000 : ℝ)|^4203 ≤ (33225362870581/100000000000000 : ℝ)^3179
        have hw : |(434566949/1000000000 : ℝ)|=(434566949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4683655557/10000000000 : ℝ)|^4203 ≤ (36683924523073/100000000000000 : ℝ)^3179
        have hw : |(4683655557/10000000000 : ℝ)|=(4683655557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403185437/1000000000 : ℝ)|^4203 ≤ (3673182689/12207031250 : ℝ)^3179
        have hw : |(403185437/1000000000 : ℝ)|=(403185437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_8 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-64543/10000000000 : ℝ)*x 0 + (1183874369/2000000000 : ℝ)*x 1 + (5920351307/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (64543/10000000000 : ℝ)^4203 ≤ (2748271/20000000000000 : ℝ)^3179 := by
    have hnat : (64543 : ℕ)^4203*20000000000000^3179 ≤ 2748271^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64543 10000000000 2748271 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1183874369/2000000000 : ℝ)^4203 ≤ (49994524416941/100000000000000 : ℝ)^3179 := by
    have hnat : (1183874369 : ℕ)^4203*100000000000000^3179 ≤ 49994524416941^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183874369 2000000000 49994524416941 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5920351307/10000000000 : ℝ)^4203 ≤ (25002730917919/50000000000000 : ℝ)^3179 := by
    have hnat : (5920351307 : ℕ)^4203*50000000000000^3179 ≤ 25002730917919^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5920351307 10000000000 25002730917919 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-64543/10000000000 : ℝ), (1183874369/2000000000 : ℝ), (5920351307/10000000000 : ℝ)] ![(2748271/20000000000000 : ℝ), (49994524416941/100000000000000 : ℝ), (25002730917919/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-64543/10000000000 : ℝ)|^4203 ≤ (2748271/20000000000000 : ℝ)^3179
        have hw : |(-64543/10000000000 : ℝ)|=(64543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1183874369/2000000000 : ℝ)|^4203 ≤ (49994524416941/100000000000000 : ℝ)^3179
        have hw : |(1183874369/2000000000 : ℝ)|=(1183874369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5920351307/10000000000 : ℝ)|^4203 ≤ (25002730917919/50000000000000 : ℝ)^3179
        have hw : |(5920351307/10000000000 : ℝ)|=(5920351307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_9 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210130139/2500000000 : ℝ)*x 0 + (-2415637647/5000000000 : ℝ)*x 1 + (1324531577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210130139/2500000000 : ℝ)^4203 ≤ (3785562668809/100000000000000 : ℝ)^3179 := by
    have hnat : (210130139 : ℕ)^4203*100000000000000^3179 ≤ 3785562668809^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210130139 2500000000 3785562668809 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2415637647/5000000000 : ℝ)^4203 ≤ (7644053163001/20000000000000 : ℝ)^3179 := by
    have hnat : (2415637647 : ℕ)^4203*20000000000000^3179 ≤ 7644053163001^3179*5000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2415637647 5000000000 7644053163001 20000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1324531577/2000000000 : ℝ)^4203 ≤ (57994171503343/100000000000000 : ℝ)^3179 := by
    have hnat : (1324531577 : ℕ)^4203*100000000000000^3179 ≤ 57994171503343^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1324531577 2000000000 57994171503343 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210130139/2500000000 : ℝ), (-2415637647/5000000000 : ℝ), (1324531577/2000000000 : ℝ)] ![(3785562668809/100000000000000 : ℝ), (7644053163001/20000000000000 : ℝ), (57994171503343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210130139/2500000000 : ℝ)|^4203 ≤ (3785562668809/100000000000000 : ℝ)^3179
        have hw : |(210130139/2500000000 : ℝ)|=(210130139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2415637647/5000000000 : ℝ)|^4203 ≤ (7644053163001/20000000000000 : ℝ)^3179
        have hw : |(-2415637647/5000000000 : ℝ)|=(2415637647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1324531577/2000000000 : ℝ)|^4203 ≤ (57994171503343/100000000000000 : ℝ)^3179
        have hw : |(1324531577/2000000000 : ℝ)|=(1324531577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_10 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (168137271/2000000000 : ℝ)*x 0 + (6623074727/10000000000 : ℝ)*x 1 + (-483071947/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168137271/2000000000 : ℝ)^4203 ≤ (3786549963193/100000000000000 : ℝ)^3179 := by
    have hnat : (168137271 : ℕ)^4203*100000000000000^3179 ≤ 3786549963193^3179*2000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168137271 2000000000 3786549963193 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6623074727/10000000000 : ℝ)^4203 ≤ (14499749402077/25000000000000 : ℝ)^3179 := by
    have hnat : (6623074727 : ℕ)^4203*25000000000000^3179 ≤ 14499749402077^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6623074727 10000000000 14499749402077 25000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483071947/1000000000 : ℝ)^4203 ≤ (38214452417389/100000000000000 : ℝ)^3179 := by
    have hnat : (483071947 : ℕ)^4203*100000000000000^3179 ≤ 38214452417389^3179*1000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483071947 1000000000 38214452417389 100000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168137271/2000000000 : ℝ), (6623074727/10000000000 : ℝ), (-483071947/1000000000 : ℝ)] ![(3786549963193/100000000000000 : ℝ), (14499749402077/25000000000000 : ℝ), (38214452417389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168137271/2000000000 : ℝ)|^4203 ≤ (3786549963193/100000000000000 : ℝ)^3179
        have hw : |(168137271/2000000000 : ℝ)|=(168137271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6623074727/10000000000 : ℝ)|^4203 ≤ (14499749402077/25000000000000 : ℝ)^3179
        have hw : |(6623074727/10000000000 : ℝ)|=(6623074727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-483071947/1000000000 : ℝ)|^4203 ≤ (38214452417389/100000000000000 : ℝ)^3179
        have hw : |(-483071947/1000000000 : ℝ)|=(483071947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1213_s2_11 (p : ℝ) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (401122537/2500000000 : ℝ)*x 0 + (5514861827/10000000000 : ℝ)*x 1 + (5518924299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (401122537/2500000000 : ℝ)^4203 ≤ (4449744763373/50000000000000 : ℝ)^3179 := by
    have hnat : (401122537 : ℕ)^4203*50000000000000^3179 ≤ 4449744763373^3179*2500000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401122537 2500000000 4449744763373 50000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5514861827/10000000000 : ℝ)^4203 ≤ (5691010272241/12500000000000 : ℝ)^3179 := by
    have hnat : (5514861827 : ℕ)^4203*12500000000000^3179 ≤ 5691010272241^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514861827 10000000000 5691010272241 12500000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5518924299/10000000000 : ℝ)^4203 ≤ (1822897131301/4000000000000 : ℝ)^3179 := by
    have hnat : (5518924299 : ℕ)^4203*4000000000000^3179 ≤ 1822897131301^3179*10000000000^4203 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518924299 10000000000 1822897131301 4000000000000 4203 3179 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4203/1024 : ℝ)) 4203 3179 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(401122537/2500000000 : ℝ), (5514861827/10000000000 : ℝ), (5518924299/10000000000 : ℝ)] ![(4449744763373/50000000000000 : ℝ), (5691010272241/12500000000000 : ℝ), (1822897131301/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(401122537/2500000000 : ℝ)|^4203 ≤ (4449744763373/50000000000000 : ℝ)^3179
        have hw : |(401122537/2500000000 : ℝ)|=(401122537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5514861827/10000000000 : ℝ)|^4203 ≤ (5691010272241/12500000000000 : ℝ)^3179
        have hw : |(5514861827/10000000000 : ℝ)|=(5514861827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5518924299/10000000000 : ℝ)|^4203 ≤ (1822897131301/4000000000000 : ℝ)^3179
        have hw : |(5518924299/10000000000 : ℝ)|=(5518924299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1213_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3019/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (469/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (163/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20123/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3019/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20123/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3019/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20123/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3019/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20123/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3019/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20123/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3019/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20123/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3019/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3019/50000 : ℝ) ^ (8405/2048 : ℝ) ≤ (496307182442069/50000000000000000000 : ℝ) := by
    have hpowers : (3019/50000 : ℝ)^8405 ≤ (496307182442069/50000000000000000000 : ℝ)^2048 := by
      have hnat : (3019 : ℕ)^8405*50000000000000000000^2048 ≤ 496307182442069^2048*50000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3019 50000 496307182442069 50000000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3019/50000 : ℝ)) (X := (496307182442069/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20123/100000 : ℝ) ^ (8405/2048 : ℝ) ≤ (17348512584564713/12500000000000000000 : ℝ) := by
    have hpowers : (20123/100000 : ℝ)^8405 ≤ (17348512584564713/12500000000000000000 : ℝ)^2048 := by
      have hnat : (20123 : ℕ)^8405*12500000000000000000^2048 ≤ 17348512584564713^2048*100000^8405 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20123 100000 17348512584564713 12500000000000000000 8405 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20123/100000 : ℝ)) (X := (17348512584564713/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000496307182442069/25000000000000000000 : ℝ) ≤ (5000024186305267/5000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (25000496307182442069/25000000000000000000 : ℝ)^2048 ≤ (5000024186305267/5000000000000000 : ℝ)^8405 := by
      have hnat : (25000496307182442069 : ℕ)^2048*5000000000000000^8405 ≤ 5000024186305267^8405*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000496307182442069 25000000000000000000 5000024186305267 5000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000024186305267/5000000000000000 : ℝ)) (X := (25000496307182442069/25000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50069890357520700921/50000000000000000000 : ℝ) ≤ (5001702080331461/5000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (50069890357520700921/50000000000000000000 : ℝ)^2048 ≤ (5001702080331461/5000000000000000 : ℝ)^8405 := by
      have hnat : (50069890357520700921 : ℕ)^2048*5000000000000000^8405 ≤ 5001702080331461^8405*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50069890357520700921 50000000000000000000 5001702080331461 5000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001702080331461/5000000000000000 : ℝ)) (X := (50069890357520700921/50000000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (6267348512584564713/6250000000000000000 : ℝ) ≤ (1000675994871531/1000000000000000 : ℝ) ^ (8405/2048 : ℝ) := by
    have hpowers : (6267348512584564713/6250000000000000000 : ℝ)^2048 ≤ (1000675994871531/1000000000000000 : ℝ)^8405 := by
      have hnat : (6267348512584564713 : ℕ)^2048*1000000000000000^8405 ≤ 1000675994871531^8405*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6267348512584564713 6250000000000000000 1000675994871531 1000000000000000 2048 8405 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000675994871531/1000000000000000 : ℝ)) (X := (6267348512584564713/6250000000000000000 : ℝ)) (by norm_num) 8405 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(496307182442069/50000000000000000000 : ℝ) ≤ ((70405078415849366951/70425000000000000000 : ℝ)+2*(838947013097/352125000000000 : ℝ)*(3019/50000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (70405078415849366951/70425000000000000000 : ℝ)+2*(838947013097/352125000000000 : ℝ)*(3019/50000 : ℝ)=(5000024186305267/5000000000000000 : ℝ) by norm_num, show 1+2*(496307182442069/50000000000000000000 : ℝ)=(25000496307182442069/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17348512584564713/12500000000000000000 : ℝ)+(496307182442069/50000000000000000000 : ℝ) ≤ ((70405078415849366951/70425000000000000000 : ℝ)+(838947013097/352125000000000 : ℝ)*((20123/100000 : ℝ)+(3019/50000 : ℝ)))^(8405/2048 : ℝ) := by
    rw [show (70405078415849366951/70425000000000000000 : ℝ)+(838947013097/352125000000000 : ℝ)*((20123/100000 : ℝ)+(3019/50000 : ℝ))=(5001702080331461/5000000000000000 : ℝ) by norm_num, show 1+(17348512584564713/12500000000000000000 : ℝ)+(496307182442069/50000000000000000000 : ℝ)=(50069890357520700921/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17348512584564713/12500000000000000000 : ℝ) ≤ ((70405078415849366951/70425000000000000000 : ℝ)+2*(838947013097/352125000000000 : ℝ)*(20123/100000 : ℝ))^(8405/2048 : ℝ) := by
    rw [show (70405078415849366951/70425000000000000000 : ℝ)+2*(838947013097/352125000000000 : ℝ)*(20123/100000 : ℝ)=(1000675994871531/1000000000000000 : ℝ) by norm_num, show 1+2*(17348512584564713/12500000000000000000 : ℝ)=(6267348512584564713/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70405078415849366951/70425000000000000000 : ℝ)*(X 1 0+X 2 0)+(838947013097/352125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (3019/50000 : ℝ)) (hi := (20123/100000 : ℝ)) (c := (70405078415849366951/70425000000000000000 : ℝ)) (alpha := (838947013097/352125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70405078415849366951/70425000000000000000 : ℝ)*(X 0 1+X 2 1)+(838947013097/352125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (3019/50000 : ℝ)) (hi := (20123/100000 : ℝ)) (c := (70405078415849366951/70425000000000000000 : ℝ)) (alpha := (838947013097/352125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70405078415849366951/70425000000000000000 : ℝ)*(X 0 2+X 1 2)+(838947013097/352125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8405/2048 : ℝ)) (lo := (3019/50000 : ℝ)) (hi := (20123/100000 : ℝ)) (c := (70405078415849366951/70425000000000000000 : ℝ)) (alpha := (838947013097/352125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529642431/2500000000 : ℝ)*X 0 0+(1099562507/2000000000 : ℝ)*X 0 1+(5170375189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((537087231/1000000000 : ℝ)*X 1 0+(-457669933/2000000000 : ℝ)*X 1 1+(5170380039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370874559/10000000000 : ℝ)*X 2 0+(2585188467/5000000000 : ℝ)*X 2 1+(-1144175371/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4345498999/10000000000 : ℝ)*X 0 0+(805495911/2000000000 : ℝ)*X 0 1+(4687989269/10000000000 : ℝ)*X 0 2+(4345498999/10000000000 : ℝ)*X 1 0+(805495911/2000000000 : ℝ)*X 1 1+(4687989269/10000000000 : ℝ)*X 1 2+(4345498999/10000000000 : ℝ)*X 2 0+(805495911/2000000000 : ℝ)*X 2 1+(4687989269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-132415813/625000000 : ℝ)*X 0 0+(2586262421/5000000000 : ℝ)*X 0 1+(5495643447/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211496333/400000000 : ℝ)*X 1 0+(-392616913/2000000000 : ℝ)*X 1 1+(5495643477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2643704253/5000000000 : ℝ)*X 2 0+(686955439/1250000000 : ℝ)*X 2 1+(-490771067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434566949/1000000000 : ℝ)*X 0 0+(4683655557/10000000000 : ℝ)*X 0 1+(403185437/1000000000 : ℝ)*X 0 2+(434566949/1000000000 : ℝ)*X 1 0+(4683655557/10000000000 : ℝ)*X 1 1+(403185437/1000000000 : ℝ)*X 1 2+(434566949/1000000000 : ℝ)*X 2 0+(4683655557/10000000000 : ℝ)*X 2 1+(403185437/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-64543/10000000000 : ℝ)*X 0 0+(1183874369/2000000000 : ℝ)*X 0 1+(5920351307/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((210130139/2500000000 : ℝ)*X 1 0+(-2415637647/5000000000 : ℝ)*X 1 1+(1324531577/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((168137271/2000000000 : ℝ)*X 2 0+(6623074727/10000000000 : ℝ)*X 2 1+(-483071947/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((401122537/2500000000 : ℝ)*X 0 0+(5514861827/10000000000 : ℝ)*X 0 1+(5518924299/10000000000 : ℝ)*X 0 2+(401122537/2500000000 : ℝ)*X 1 0+(5514861827/10000000000 : ℝ)*X 1 1+(5518924299/10000000000 : ℝ)*X 1 2+(401122537/2500000000 : ℝ)*X 2 0+(5514861827/10000000000 : ℝ)*X 2 1+(5518924299/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1213_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (111761551567431566310869083/48906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4181803/1250000000000 : ℝ)*(lower2) + (20141449/12500000000000 : ℝ)*(upper3) + (213052921/100000000000000 : ℝ)*(upper4) + (285505698584199/12500000000000 : ℝ)*(major0) + (285505698584199/12500000000000 : ℝ)*(major1) + (285505698584199/12500000000000 : ℝ)*(major2) + (305404602375691/10000000000000 : ℝ)*(sp0) + (381760399481763/12500000000000 : ℝ)*(sp1) + (1527033255244953/50000000000000 : ℝ)*(sp2) + (756996074269617/50000000000000 : ℝ)*(sp3) + (34558337531/100000000000000 : ℝ)*(sp4) + (16685364199/100000000000000 : ℝ)*(sp6) + (15756779831/100000000000000 : ℝ)*(sp7) + (1306879831/50000000000000 : ℝ)*(sp8) + (302801581063813/20000000000000 : ℝ)*(f.failure) + (381760399481763/12500000000000 : ℝ)*(f.sum) + (142958748753859/11737500000000000000000000000 : ℝ)*base66 + (195766849576368861/97812500000000000000000000000000 : ℝ)*base67 + (957987881034493861/97812500000000000000000000000000 : ℝ)*base69 + (355747280305193639/97812500000000000000000000000000 : ℝ)*base72 + (15076426265843/23475000000000000000000000000 : ℝ)*base74 + (243798749176443639/97812500000000000000000000000000 : ℝ)*base76 + (1362112500681443639/97812500000000000000000000000000 : ℝ)*base78 + (475699016908006139/97812500000000000000000000000000 : ℝ)*base80 + (15677671540379/2934375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (270047/500000000000000000000 : ℝ)*base89 + (270047/500000000000000000000 : ℝ)*base91 + (270047/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1822462405404803284262469891/391250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2314526260930059/100000000000000 : ℝ)*(major0) + (2314526260930059/100000000000000 : ℝ)*(major1) + (2314526260930059/100000000000000 : ℝ)*(major2) + (120520201/20000000000000 : ℝ)*(sp1) + (893098329/50000000000000 : ℝ)*(sp2) + (78507011/10000000000000 : ℝ)*(sp3) + (773709787312609/25000000000000 : ℝ)*(sp4) + (309483896668317/10000000000000 : ℝ)*(sp5) + (309483763488313/10000000000000 : ℝ)*(sp6) + (1534211121261171/100000000000000 : ℝ)*(sp7) + (205231943/25000000000000 : ℝ)*(sp8) + (200447017/50000000000000 : ℝ)*(sp9) + (549098421/100000000000000 : ℝ)*(sp10) + (245041129/50000000000000 : ℝ)*(sp11) + (76710619820677/5000000000000 : ℝ)*(f.failure) + (96713749068069/3125000000000 : ℝ)*(f.sum) + (894223607077/733593750000000000000000000 : ℝ)*base65 + (8526118891254908901/782500000000000000000000000000000 : ℝ)*base67 + (6714286478557408901/782500000000000000000000000000000 : ℝ)*base69 + (2976896934282408901/782500000000000000000000000000000 : ℝ)*base71 + (5316334606079/1467187500000000000000000000 : ℝ)*base73 + (2714937993739908901/782500000000000000000000000000000 : ℝ)*base75 + (625603098059908901/782500000000000000000000000000000 : ℝ)*base77 + (3134823201727408901/782500000000000000000000000000000 : ℝ)*base79 + (46112658965591/5868750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (33263/125000000000000000000 : ℝ)*base89 + (33263/125000000000000000000 : ℝ)*base91 + (33263/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1213_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20123/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3019/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (469/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (163/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1213_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1213_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (469/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (163/1000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1213_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1213_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1213_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8405/2048 : ℝ) ≤ p) (hpb : p ≤ (4203/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37715219/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (469/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (163/1000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1213_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
