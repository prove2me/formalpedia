-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1125_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:06.146476+00:00
-- url     : https://prove2.me/submissions/7e6b8b07-80b7-456e-9cbd-202602e6c2c9

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
theorem support_rectangle_w1125_s0_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1897202911/10000000000 : ℝ)*x 0 + (605826779/1000000000 : ℝ)*x 1 + (1194579591/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1897202911/10000000000 : ℝ)^4159 ≤ (11023528889207/100000000000000 : ℝ)^3135 := by
    have hnat : (1897202911 : ℕ)^4159*100000000000000^3135 ≤ 11023528889207^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1897202911 10000000000 11023528889207 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605826779/1000000000 : ℝ)^4159 ≤ (10286932818327/20000000000000 : ℝ)^3135 := by
    have hnat : (605826779 : ℕ)^4159*20000000000000^3135 ≤ 10286932818327^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605826779 1000000000 10286932818327 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1194579591/2500000000 : ℝ)^4159 ≤ (7508361398693/20000000000000 : ℝ)^3135 := by
    have hnat : (1194579591 : ℕ)^4159*20000000000000^3135 ≤ 7508361398693^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1194579591 2500000000 7508361398693 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1897202911/10000000000 : ℝ), (605826779/1000000000 : ℝ), (1194579591/2500000000 : ℝ)] ![(11023528889207/100000000000000 : ℝ), (10286932818327/20000000000000 : ℝ), (7508361398693/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1897202911/10000000000 : ℝ)|^4159 ≤ (11023528889207/100000000000000 : ℝ)^3135
        have hw : |(-1897202911/10000000000 : ℝ)|=(1897202911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605826779/1000000000 : ℝ)|^4159 ≤ (10286932818327/20000000000000 : ℝ)^3135
        have hw : |(605826779/1000000000 : ℝ)|=(605826779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1194579591/2500000000 : ℝ)|^4159 ≤ (7508361398693/20000000000000 : ℝ)^3135
        have hw : |(1194579591/2500000000 : ℝ)|=(1194579591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s0_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5517751297/10000000000 : ℝ)*x 0 + (-2632232357/10000000000 : ℝ)*x 1 + (119457961/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5517751297/10000000000 : ℝ)^4159 ≤ (11359328536671/25000000000000 : ℝ)^3135 := by
    have hnat : (5517751297 : ℕ)^4159*25000000000000^3135 ≤ 11359328536671^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5517751297 10000000000 11359328536671 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632232357/10000000000 : ℝ)^4159 ≤ (3404175610691/20000000000000 : ℝ)^3135 := by
    have hnat : (2632232357 : ℕ)^4159*20000000000000^3135 ≤ 3404175610691^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632232357 10000000000 3404175610691 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119457961/250000000 : ℝ)^4159 ≤ (37541807785611/100000000000000 : ℝ)^3135 := by
    have hnat : (119457961 : ℕ)^4159*100000000000000^3135 ≤ 37541807785611^3135*250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119457961 250000000 37541807785611 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5517751297/10000000000 : ℝ), (-2632232357/10000000000 : ℝ), (119457961/250000000 : ℝ)] ![(11359328536671/25000000000000 : ℝ), (3404175610691/20000000000000 : ℝ), (37541807785611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5517751297/10000000000 : ℝ)|^4159 ≤ (11359328536671/25000000000000 : ℝ)^3135
        have hw : |(5517751297/10000000000 : ℝ)|=(5517751297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2632232357/10000000000 : ℝ)|^4159 ≤ (3404175610691/20000000000000 : ℝ)^3135
        have hw : |(-2632232357/10000000000 : ℝ)|=(2632232357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119457961/250000000 : ℝ)|^4159 ≤ (37541807785611/100000000000000 : ℝ)^3135
        have hw : |(119457961/250000000 : ℝ)|=(119457961/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s0_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1103550241/2000000000 : ℝ)*x 0 + (4778318481/10000000000 : ℝ)*x 1 + (-329029053/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1103550241/2000000000 : ℝ)^4159 ≤ (45437313141629/100000000000000 : ℝ)^3135 := by
    have hnat : (1103550241 : ℕ)^4159*100000000000000^3135 ≤ 45437313141629^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103550241 2000000000 45437313141629 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4778318481/10000000000 : ℝ)^4159 ≤ (37541808212953/100000000000000 : ℝ)^3135 := by
    have hnat : (4778318481 : ℕ)^4159*100000000000000^3135 ≤ 37541808212953^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4778318481 10000000000 37541808212953 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329029053/1250000000 : ℝ)^4159 ≤ (17020878628211/100000000000000 : ℝ)^3135 := by
    have hnat : (329029053 : ℕ)^4159*100000000000000^3135 ≤ 17020878628211^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329029053 1250000000 17020878628211 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1103550241/2000000000 : ℝ), (4778318481/10000000000 : ℝ), (-329029053/1250000000 : ℝ)] ![(45437313141629/100000000000000 : ℝ), (37541808212953/100000000000000 : ℝ), (17020878628211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1103550241/2000000000 : ℝ)|^4159 ≤ (45437313141629/100000000000000 : ℝ)^3135
        have hw : |(1103550241/2000000000 : ℝ)|=(1103550241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4778318481/10000000000 : ℝ)|^4159 ≤ (37541808212953/100000000000000 : ℝ)^3135
        have hw : |(4778318481/10000000000 : ℝ)|=(4778318481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-329029053/1250000000 : ℝ)|^4159 ≤ (17020878628211/100000000000000 : ℝ)^3135
        have hw : |(-329029053/1250000000 : ℝ)|=(329029053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s0_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4202369317/10000000000 : ℝ)*x 0 + (312187899/1000000000 : ℝ)*x 1 + (5659817033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4202369317/10000000000 : ℝ)^4159 ≤ (15830124912127/50000000000000 : ℝ)^3135 := by
    have hnat : (4202369317 : ℕ)^4159*50000000000000^3135 ≤ 15830124912127^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4202369317 10000000000 15830124912127 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (312187899/1000000000 : ℝ)^4159 ≤ (21343948938631/100000000000000 : ℝ)^3135 := by
    have hnat : (312187899 : ℕ)^4159*100000000000000^3135 ≤ 21343948938631^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312187899 1000000000 21343948938631 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5659817033/10000000000 : ℝ)^4159 ≤ (2937237576609/6250000000000 : ℝ)^3135 := by
    have hnat : (5659817033 : ℕ)^4159*6250000000000^3135 ≤ 2937237576609^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5659817033 10000000000 2937237576609 6250000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4202369317/10000000000 : ℝ), (312187899/1000000000 : ℝ), (5659817033/10000000000 : ℝ)] ![(15830124912127/50000000000000 : ℝ), (21343948938631/100000000000000 : ℝ), (2937237576609/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4202369317/10000000000 : ℝ)|^4159 ≤ (15830124912127/50000000000000 : ℝ)^3135
        have hw : |(4202369317/10000000000 : ℝ)|=(4202369317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(312187899/1000000000 : ℝ)|^4159 ≤ (21343948938631/100000000000000 : ℝ)^3135
        have hw : |(312187899/1000000000 : ℝ)|=(312187899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5659817033/10000000000 : ℝ)|^4159 ≤ (2937237576609/6250000000000 : ℝ)^3135
        have hw : |(5659817033/10000000000 : ℝ)|=(5659817033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s0_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-951199317/5000000000 : ℝ)*x 0 + (2405672839/5000000000 : ℝ)*x 1 + (3012040321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951199317/5000000000 : ℝ)^4159 ≤ (5531798474299/50000000000000 : ℝ)^3135 := by
    have hnat : (951199317 : ℕ)^4159*50000000000000^3135 ≤ 5531798474299^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951199317 5000000000 5531798474299 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2405672839/5000000000 : ℝ)^4159 ≤ (18943218835611/50000000000000 : ℝ)^3135 := by
    have hnat : (2405672839 : ℕ)^4159*50000000000000^3135 ≤ 18943218835611^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2405672839 5000000000 18943218835611 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3012040321/5000000000 : ℝ)^4159 ≤ (25524982683769/50000000000000 : ℝ)^3135 := by
    have hnat : (3012040321 : ℕ)^4159*50000000000000^3135 ≤ 25524982683769^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3012040321 5000000000 25524982683769 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-951199317/5000000000 : ℝ), (2405672839/5000000000 : ℝ), (3012040321/5000000000 : ℝ)] ![(5531798474299/50000000000000 : ℝ), (18943218835611/50000000000000 : ℝ), (25524982683769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-951199317/5000000000 : ℝ)|^4159 ≤ (5531798474299/50000000000000 : ℝ)^3135
        have hw : |(-951199317/5000000000 : ℝ)|=(951199317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2405672839/5000000000 : ℝ)|^4159 ≤ (18943218835611/50000000000000 : ℝ)^3135
        have hw : |(2405672839/5000000000 : ℝ)|=(2405672839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3012040321/5000000000 : ℝ)|^4159 ≤ (25524982683769/50000000000000 : ℝ)^3135
        have hw : |(3012040321/5000000000 : ℝ)|=(3012040321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s0_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5170045187/10000000000 : ℝ)*x 0 + (-693235127/5000000000 : ℝ)*x 1 + (6024080577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170045187/10000000000 : ℝ)^4159 ≤ (4167845663669/10000000000000 : ℝ)^3135 := by
    have hnat : (5170045187 : ℕ)^4159*10000000000000^3135 ≤ 4167845663669^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170045187 10000000000 4167845663669 10000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693235127/5000000000 : ℝ)^4159 ≤ (3635789355581/50000000000000 : ℝ)^3135 := by
    have hnat : (693235127 : ℕ)^4159*50000000000000^3135 ≤ 3635789355581^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693235127 5000000000 3635789355581 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6024080577/10000000000 : ℝ)^4159 ≤ (51049964636787/100000000000000 : ℝ)^3135 := by
    have hnat : (6024080577 : ℕ)^4159*100000000000000^3135 ≤ 51049964636787^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6024080577 10000000000 51049964636787 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170045187/10000000000 : ℝ), (-693235127/5000000000 : ℝ), (6024080577/10000000000 : ℝ)] ![(4167845663669/10000000000000 : ℝ), (3635789355581/50000000000000 : ℝ), (51049964636787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170045187/10000000000 : ℝ)|^4159 ≤ (4167845663669/10000000000000 : ℝ)^3135
        have hw : |(5170045187/10000000000 : ℝ)|=(5170045187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-693235127/5000000000 : ℝ)|^4159 ≤ (3635789355581/50000000000000 : ℝ)^3135
        have hw : |(-693235127/5000000000 : ℝ)|=(693235127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6024080577/10000000000 : ℝ)|^4159 ≤ (51049964636787/100000000000000 : ℝ)^3135
        have hw : |(6024080577/10000000000 : ℝ)|=(6024080577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s0_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2585022609/5000000000 : ℝ)*x 0 + (1506020141/2500000000 : ℝ)*x 1 + (-346617557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585022609/5000000000 : ℝ)^4159 ≤ (20839228484113/50000000000000 : ℝ)^3135 := by
    have hnat : (2585022609 : ℕ)^4159*50000000000000^3135 ≤ 20839228484113^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585022609 5000000000 20839228484113 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1506020141/2500000000 : ℝ)^4159 ≤ (51049964490637/100000000000000 : ℝ)^3135 := by
    have hnat : (1506020141 : ℕ)^4159*100000000000000^3135 ≤ 51049964490637^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1506020141 2500000000 51049964490637 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346617557/2500000000 : ℝ)^4159 ≤ (7271578530261/100000000000000 : ℝ)^3135 := by
    have hnat : (346617557 : ℕ)^4159*100000000000000^3135 ≤ 7271578530261^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346617557 2500000000 7271578530261 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585022609/5000000000 : ℝ), (1506020141/2500000000 : ℝ), (-346617557/2500000000 : ℝ)] ![(20839228484113/50000000000000 : ℝ), (51049964490637/100000000000000 : ℝ), (7271578530261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585022609/5000000000 : ℝ)|^4159 ≤ (20839228484113/50000000000000 : ℝ)^3135
        have hw : |(2585022609/5000000000 : ℝ)|=(2585022609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1506020141/2500000000 : ℝ)|^4159 ≤ (51049964490637/100000000000000 : ℝ)^3135
        have hw : |(1506020141/2500000000 : ℝ)|=(1506020141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-346617557/2500000000 : ℝ)|^4159 ≤ (7271578530261/100000000000000 : ℝ)^3135
        have hw : |(-346617557/2500000000 : ℝ)|=(346617557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s0_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4212671799/10000000000 : ℝ)*x 0 + (5594329087/10000000000 : ℝ)*x 1 + (3189666909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4212671799/10000000000 : ℝ)^4159 ≤ (31763261657411/100000000000000 : ℝ)^3135 := by
    have hnat : (4212671799 : ℕ)^4159*100000000000000^3135 ≤ 31763261657411^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4212671799 10000000000 31763261657411 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5594329087/10000000000 : ℝ)^4159 ≤ (9255155832307/20000000000000 : ℝ)^3135 := by
    have hnat : (5594329087 : ℕ)^4159*20000000000000^3135 ≤ 9255155832307^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5594329087 10000000000 9255155832307 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3189666909/10000000000 : ℝ)^4159 ≤ (4392191833183/20000000000000 : ℝ)^3135 := by
    have hnat : (3189666909 : ℕ)^4159*20000000000000^3135 ≤ 4392191833183^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3189666909 10000000000 4392191833183 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4212671799/10000000000 : ℝ), (5594329087/10000000000 : ℝ), (3189666909/10000000000 : ℝ)] ![(31763261657411/100000000000000 : ℝ), (9255155832307/20000000000000 : ℝ), (4392191833183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4212671799/10000000000 : ℝ)|^4159 ≤ (31763261657411/100000000000000 : ℝ)^3135
        have hw : |(4212671799/10000000000 : ℝ)|=(4212671799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5594329087/10000000000 : ℝ)|^4159 ≤ (9255155832307/20000000000000 : ℝ)^3135
        have hw : |(5594329087/10000000000 : ℝ)|=(5594329087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3189666909/10000000000 : ℝ)|^4159 ≤ (4392191833183/20000000000000 : ℝ)^3135
        have hw : |(3189666909/10000000000 : ℝ)|=(3189666909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (343/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (697/2500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8317/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8317 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8317*1^2048 ≤ 0^2048*1^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8317/2048 : ℝ) ≤ (151297465208989947/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8317 ≤ (151297465208989947/6250000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8317*6250000000000000000^2048 ≤ 151297465208989947^2048*5^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 151297465208989947 6250000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (151297465208989947/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8317 := by
      have hnat : (1 : ℕ)^2048*1^8317 ≤ 1^8317*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6401297465208989947/6250000000000000000 : ℝ) ≤ (251476828811133/250000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (6401297465208989947/6250000000000000000 : ℝ)^2048 ≤ (251476828811133/250000000000000 : ℝ)^8317 := by
      have hnat : (6401297465208989947 : ℕ)^2048*250000000000000^8317 ≤ 251476828811133^8317*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6401297465208989947 6250000000000000000 251476828811133 250000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251476828811133/250000000000000 : ℝ)) (X := (6401297465208989947/6250000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3276297465208989947/3125000000000000000 : ℝ) ≤ (126476828811133/125000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (3276297465208989947/3125000000000000000 : ℝ)^2048 ≤ (126476828811133/125000000000000 : ℝ)^8317 := by
      have hnat : (3276297465208989947 : ℕ)^2048*125000000000000^8317 ≤ 126476828811133^8317*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3276297465208989947 3125000000000000000 126476828811133 125000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (126476828811133/125000000000000 : ℝ)) (X := (3276297465208989947/3125000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1476828811133/100000000000000 : ℝ)*(0 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(1476828811133/100000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(151297465208989947/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1476828811133/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (1 : ℝ)+(1476828811133/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(251476828811133/250000000000000 : ℝ) by norm_num, show 1+(151297465208989947/6250000000000000000 : ℝ)+(0 : ℝ)=(6401297465208989947/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(151297465208989947/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1476828811133/100000000000000 : ℝ)*(2/5 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(1476828811133/100000000000000 : ℝ)*(2/5 : ℝ)=(126476828811133/125000000000000 : ℝ) by norm_num, show 1+2*(151297465208989947/6250000000000000000 : ℝ)=(3276297465208989947/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1476828811133/100000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1476828811133/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1476828811133/100000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1476828811133/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1476828811133/100000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1476828811133/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1897202911/10000000000 : ℝ)*X 0 0+(605826779/1000000000 : ℝ)*X 0 1+(1194579591/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5517751297/10000000000 : ℝ)*X 1 0+(-2632232357/10000000000 : ℝ)*X 1 1+(119457961/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1103550241/2000000000 : ℝ)*X 2 0+(4778318481/10000000000 : ℝ)*X 2 1+(-329029053/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4202369317/10000000000 : ℝ)*X 0 0+(312187899/1000000000 : ℝ)*X 0 1+(5659817033/10000000000 : ℝ)*X 0 2+(4202369317/10000000000 : ℝ)*X 1 0+(312187899/1000000000 : ℝ)*X 1 1+(5659817033/10000000000 : ℝ)*X 1 2+(4202369317/10000000000 : ℝ)*X 2 0+(312187899/1000000000 : ℝ)*X 2 1+(5659817033/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-951199317/5000000000 : ℝ)*X 0 0+(2405672839/5000000000 : ℝ)*X 0 1+(3012040321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5170045187/10000000000 : ℝ)*X 1 0+(-693235127/5000000000 : ℝ)*X 1 1+(6024080577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585022609/5000000000 : ℝ)*X 2 0+(1506020141/2500000000 : ℝ)*X 2 1+(-346617557/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4212671799/10000000000 : ℝ)*X 0 0+(5594329087/10000000000 : ℝ)*X 0 1+(3189666909/10000000000 : ℝ)*X 0 2+(4212671799/10000000000 : ℝ)*X 1 0+(5594329087/10000000000 : ℝ)*X 1 1+(3189666909/10000000000 : ℝ)*X 1 2+(4212671799/10000000000 : ℝ)*X 2 0+(5594329087/10000000000 : ℝ)*X 2 1+(3189666909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15950908006680217375167/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16652991/25000000000000 : ℝ)*(base1) + (1611429141/100000000000000 : ℝ)*(base19) + (746454459/50000000000000 : ℝ)*(base23) + (105493447/100000000000000 : ℝ)*(base24) + (372082269/100000000000000 : ℝ)*(upper3) + (293828811959011/50000000000000 : ℝ)*(major0) + (293828811959011/50000000000000 : ℝ)*(major1) + (293828811959011/50000000000000 : ℝ)*(major2) + (781286296667777/100000000000000 : ℝ)*(sp0) + (39064408920027/5000000000000 : ℝ)*(sp1) + (781288191427317/100000000000000 : ℝ)*(sp2) + (197011165996217/50000000000000 : ℝ)*(sp3) + (3559773867/100000000000000 : ℝ)*(sp4) + (2846723187/100000000000000 : ℝ)*(sp7) + (12313288916487/3125000000000 : ℝ)*(f.failure) + (781289789829681/100000000000000 : ℝ)*(f.sum) + (10717279695537/2500000000000000000000000000 : ℝ)*base66 + (30063848544463/5000000000000000000000000000 : ℝ)*base67 + (3850077265537/5000000000000000000000000000 : ℝ)*base70 + (5415099614463/5000000000000000000000000000 : ℝ)*base71 + (7773966403037/2500000000000000000000000000 : ℝ)*base74 + (10901831944463/5000000000000000000000000000 : ℝ)*base75 + (4965733410537/5000000000000000000000000000 : ℝ)*base78 + (5993880560537/5000000000000000000000000000 : ℝ)*base80 + (13948445773037/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base87 + (281/2500000000000000000 : ℝ)*base90 + (281/2500000000000000000 : ℝ)*base92 + (281/2500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (555033149413192800519/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16994531/50000000000000 : ℝ)*(base1) + (535507939/100000000000000 : ℝ)*(base19) + (269886351/50000000000000 : ℝ)*(base23) + (3432243/6250000000000 : ℝ)*(upper3) + (16177341/25000000000000 : ℝ)*(upper5) + (31011035542631/5000000000000 : ℝ)*(major0) + (31011035542631/5000000000000 : ℝ)*(major1) + (31011035542631/5000000000000 : ℝ)*(major2) + (53044911/5000000000000 : ℝ)*(sp1) + (1050795161/100000000000000 : ℝ)*(sp2) + (412291270886419/50000000000000 : ℝ)*(sp4) + (824580911377617/100000000000000 : ℝ)*(sp5) + (103072614651989/12500000000000 : ℝ)*(sp6) + (415858805927977/100000000000000 : ℝ)*(sp7) + (415858839917039/100000000000000 : ℝ)*(f.failure) + (25768203368243/3125000000000 : ℝ)*(f.sum) + (1389578173/250000000000000000000000000 : ℝ)*base65 + (1216361670577/500000000000000000000000000 : ℝ)*base68 + (568438633577/500000000000000000000000000 : ℝ)*base70 + (269426760077/500000000000000000000000000 : ℝ)*base72 + (917370524327/250000000000000000000000000 : ℝ)*base74 + (5074451459923/500000000000000000000000000 : ℝ)*base75 + (2818244688923/500000000000000000000000000 : ℝ)*base77 + (5056983006923/500000000000000000000000000 : ℝ)*base79 + (1270692312327/250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (161343/80000000000000000000 : ℝ)*base89 + (161343/80000000000000000000 : ℝ)*base91 + (161343/80000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1125_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (697/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1125_s1_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21031/100000 : ℝ)*x 0 + (5706069411/10000000000 : ℝ)*x 1 + (4998694259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21031/100000 : ℝ)^4159 ≤ (3159529682393/25000000000000 : ℝ)^3135 := by
    have hnat : (21031 : ℕ)^4159*25000000000000^3135 ≤ 3159529682393^3135*100000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21031 100000 3159529682393 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5706069411/10000000000 : ℝ)^4159 ≤ (9501195507549/20000000000000 : ℝ)^3135 := by
    have hnat : (5706069411 : ℕ)^4159*20000000000000^3135 ≤ 9501195507549^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5706069411 10000000000 9501195507549 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998694259/10000000000 : ℝ)^4159 ≤ (2490993982639/6250000000000 : ℝ)^3135 := by
    have hnat : (4998694259 : ℕ)^4159*6250000000000^3135 ≤ 2490993982639^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998694259 10000000000 2490993982639 6250000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21031/100000 : ℝ), (5706069411/10000000000 : ℝ), (4998694259/10000000000 : ℝ)] ![(3159529682393/25000000000000 : ℝ), (9501195507549/20000000000000 : ℝ), (2490993982639/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21031/100000 : ℝ)|^4159 ≤ (3159529682393/25000000000000 : ℝ)^3135
        have hw : |(-21031/100000 : ℝ)|=(21031/100000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5706069411/10000000000 : ℝ)|^4159 ≤ (9501195507549/20000000000000 : ℝ)^3135
        have hw : |(5706069411/10000000000 : ℝ)|=(5706069411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998694259/10000000000 : ℝ)|^4159 ≤ (2490993982639/6250000000000 : ℝ)^3135
        have hw : |(4998694259/10000000000 : ℝ)|=(4998694259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s1_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2710027369/5000000000 : ℝ)*x 0 + (-310646319/1250000000 : ℝ)*x 1 + (4998693937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710027369/5000000000 : ℝ)^4159 ≤ (8874625173077/20000000000000 : ℝ)^3135 := by
    have hnat : (2710027369 : ℕ)^4159*20000000000000^3135 ≤ 8874625173077^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710027369 5000000000 8874625173077 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (310646319/1250000000 : ℝ)^4159 ≤ (7885486906833/50000000000000 : ℝ)^3135 := by
    have hnat : (310646319 : ℕ)^4159*50000000000000^3135 ≤ 7885486906833^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      310646319 1250000000 7885486906833 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4998693937/10000000000 : ℝ)^4159 ≤ (19927950158117/50000000000000 : ℝ)^3135 := by
    have hnat : (4998693937 : ℕ)^4159*50000000000000^3135 ≤ 19927950158117^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998693937 10000000000 19927950158117 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710027369/5000000000 : ℝ), (-310646319/1250000000 : ℝ), (4998693937/10000000000 : ℝ)] ![(8874625173077/20000000000000 : ℝ), (7885486906833/50000000000000 : ℝ), (19927950158117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710027369/5000000000 : ℝ)|^4159 ≤ (8874625173077/20000000000000 : ℝ)^3135
        have hw : |(2710027369/5000000000 : ℝ)|=(2710027369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-310646319/1250000000 : ℝ)|^4159 ≤ (7885486906833/50000000000000 : ℝ)^3135
        have hw : |(-310646319/1250000000 : ℝ)|=(310646319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4998693937/10000000000 : ℝ)|^4159 ≤ (19927950158117/50000000000000 : ℝ)^3135
        have hw : |(4998693937/10000000000 : ℝ)|=(4998693937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s1_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5420056353/10000000000 : ℝ)*x 0 + (4998692469/10000000000 : ℝ)*x 1 + (-2485170311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5420056353/10000000000 : ℝ)^4159 ≤ (44373143405817/100000000000000 : ℝ)^3135 := by
    have hnat : (5420056353 : ℕ)^4159*100000000000000^3135 ≤ 44373143405817^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5420056353 10000000000 44373143405817 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4998692469/10000000000 : ℝ)^4159 ≤ (39855884788307/100000000000000 : ℝ)^3135 := by
    have hnat : (4998692469 : ℕ)^4159*100000000000000^3135 ≤ 39855884788307^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998692469 10000000000 39855884788307 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2485170311/10000000000 : ℝ)^4159 ≤ (15770971784719/100000000000000 : ℝ)^3135 := by
    have hnat : (2485170311 : ℕ)^4159*100000000000000^3135 ≤ 15770971784719^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2485170311 10000000000 15770971784719 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5420056353/10000000000 : ℝ), (4998692469/10000000000 : ℝ), (-2485170311/10000000000 : ℝ)] ![(44373143405817/100000000000000 : ℝ), (39855884788307/100000000000000 : ℝ), (15770971784719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5420056353/10000000000 : ℝ)|^4159 ≤ (44373143405817/100000000000000 : ℝ)^3135
        have hw : |(5420056353/10000000000 : ℝ)|=(5420056353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4998692469/10000000000 : ℝ)|^4159 ≤ (39855884788307/100000000000000 : ℝ)^3135
        have hw : |(4998692469/10000000000 : ℝ)|=(4998692469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2485170311/10000000000 : ℝ)|^4159 ≤ (15770971784719/100000000000000 : ℝ)^3135
        have hw : |(-2485170311/10000000000 : ℝ)|=(2485170311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s1_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079719039/2500000000 : ℝ)*x 0 + (3673845183/10000000000 : ℝ)*x 1 + (5076456783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079719039/2500000000 : ℝ)^4159 ≤ (2051871586913/6250000000000 : ℝ)^3135 := by
    have hnat : (1079719039 : ℕ)^4159*6250000000000^3135 ≤ 2051871586913^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079719039 2500000000 2051871586913 6250000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3673845183/10000000000 : ℝ)^4159 ≤ (5297905366401/20000000000000 : ℝ)^3135 := by
    have hnat : (3673845183 : ℕ)^4159*20000000000000^3135 ≤ 5297905366401^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3673845183 10000000000 5297905366401 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5076456783/10000000000 : ℝ)^4159 ≤ (40680527752831/100000000000000 : ℝ)^3135 := by
    have hnat : (5076456783 : ℕ)^4159*100000000000000^3135 ≤ 40680527752831^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5076456783 10000000000 40680527752831 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079719039/2500000000 : ℝ), (3673845183/10000000000 : ℝ), (5076456783/10000000000 : ℝ)] ![(2051871586913/6250000000000 : ℝ), (5297905366401/20000000000000 : ℝ), (40680527752831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079719039/2500000000 : ℝ)|^4159 ≤ (2051871586913/6250000000000 : ℝ)^3135
        have hw : |(1079719039/2500000000 : ℝ)|=(1079719039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3673845183/10000000000 : ℝ)|^4159 ≤ (5297905366401/20000000000000 : ℝ)^3135
        have hw : |(3673845183/10000000000 : ℝ)|=(3673845183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5076456783/10000000000 : ℝ)|^4159 ≤ (40680527752831/100000000000000 : ℝ)^3135
        have hw : |(5076456783/10000000000 : ℝ)|=(5076456783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s1_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2103930239/10000000000 : ℝ)*x 0 + (1001683113/2000000000 : ℝ)*x 1 + (5696154347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2103930239/10000000000 : ℝ)^4159 ≤ (12348376877/97656250000 : ℝ)^3135 := by
    have hnat : (2103930239 : ℕ)^4159*97656250000^3135 ≤ 12348376877^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2103930239 10000000000 12348376877 97656250000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1001683113/2000000000 : ℝ)^4159 ≤ (39958764530331/100000000000000 : ℝ)^3135 := by
    have hnat : (1001683113 : ℕ)^4159*100000000000000^3135 ≤ 39958764530331^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001683113 2000000000 39958764530331 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5696154347/10000000000 : ℝ)^4159 ≤ (9479299507307/20000000000000 : ℝ)^3135 := by
    have hnat : (5696154347 : ℕ)^4159*20000000000000^3135 ≤ 9479299507307^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5696154347 10000000000 9479299507307 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2103930239/10000000000 : ℝ), (1001683113/2000000000 : ℝ), (5696154347/10000000000 : ℝ)] ![(12348376877/97656250000 : ℝ), (39958764530331/100000000000000 : ℝ), (9479299507307/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2103930239/10000000000 : ℝ)|^4159 ≤ (12348376877/97656250000 : ℝ)^3135
        have hw : |(-2103930239/10000000000 : ℝ)|=(2103930239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1001683113/2000000000 : ℝ)|^4159 ≤ (39958764530331/100000000000000 : ℝ)^3135
        have hw : |(1001683113/2000000000 : ℝ)|=(1001683113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5696154347/10000000000 : ℝ)|^4159 ≤ (9479299507307/20000000000000 : ℝ)^3135
        have hw : |(5696154347/10000000000 : ℝ)|=(5696154347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s1_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10232133/19531250 : ℝ)*x 0 + (-1787709769/10000000000 : ℝ)*x 1 + (1139230821/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10232133/19531250 : ℝ)^4159 ≤ (21207960342129/50000000000000 : ℝ)^3135 := by
    have hnat : (10232133 : ℕ)^4159*50000000000000^3135 ≤ 21207960342129^3135*19531250^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10232133 19531250 21207960342129 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1787709769/10000000000 : ℝ)^4159 ≤ (318362013619/3125000000000 : ℝ)^3135 := by
    have hnat : (1787709769 : ℕ)^4159*3125000000000^3135 ≤ 318362013619^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787709769 10000000000 318362013619 3125000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1139230821/2000000000 : ℝ)^4159 ≤ (47396494865183/100000000000000 : ℝ)^3135 := by
    have hnat : (1139230821 : ℕ)^4159*100000000000000^3135 ≤ 47396494865183^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1139230821 2000000000 47396494865183 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10232133/19531250 : ℝ), (-1787709769/10000000000 : ℝ), (1139230821/2000000000 : ℝ)] ![(21207960342129/50000000000000 : ℝ), (318362013619/3125000000000 : ℝ), (47396494865183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10232133/19531250 : ℝ)|^4159 ≤ (21207960342129/50000000000000 : ℝ)^3135
        have hw : |(10232133/19531250 : ℝ)|=(10232133/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1787709769/10000000000 : ℝ)|^4159 ≤ (318362013619/3125000000000 : ℝ)^3135
        have hw : |(-1787709769/10000000000 : ℝ)|=(1787709769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1139230821/2000000000 : ℝ)|^4159 ≤ (47396494865183/100000000000000 : ℝ)^3135
        have hw : |(1139230821/2000000000 : ℝ)|=(1139230821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s1_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1047770427/2000000000 : ℝ)*x 0 + (1424038567/2500000000 : ℝ)*x 1 + (-71508379/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047770427/2000000000 : ℝ)^4159 ≤ (42415921103157/100000000000000 : ℝ)^3135 := by
    have hnat : (1047770427 : ℕ)^4159*100000000000000^3135 ≤ 42415921103157^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047770427 2000000000 42415921103157 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1424038567/2500000000 : ℝ)^4159 ≤ (23698248332241/50000000000000 : ℝ)^3135 := by
    have hnat : (1424038567 : ℕ)^4159*50000000000000^3135 ≤ 23698248332241^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1424038567 2500000000 23698248332241 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71508379/400000000 : ℝ)^4159 ≤ (2546895553287/25000000000000 : ℝ)^3135 := by
    have hnat : (71508379 : ℕ)^4159*25000000000000^3135 ≤ 2546895553287^3135*400000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71508379 400000000 2546895553287 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047770427/2000000000 : ℝ), (1424038567/2500000000 : ℝ), (-71508379/400000000 : ℝ)] ![(42415921103157/100000000000000 : ℝ), (23698248332241/50000000000000 : ℝ), (2546895553287/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047770427/2000000000 : ℝ)|^4159 ≤ (42415921103157/100000000000000 : ℝ)^3135
        have hw : |(1047770427/2000000000 : ℝ)|=(1047770427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1424038567/2500000000 : ℝ)|^4159 ≤ (23698248332241/50000000000000 : ℝ)^3135
        have hw : |(1424038567/2500000000 : ℝ)|=(1424038567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71508379/400000000 : ℝ)|^4159 ≤ (2546895553287/25000000000000 : ℝ)^3135
        have hw : |(-71508379/400000000 : ℝ)|=(71508379/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s1_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4320519793/10000000000 : ℝ)*x 0 + (632147721/1250000000 : ℝ)*x 1 + (923376041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4320519793/10000000000 : ℝ)^4159 ≤ (16423260770603/50000000000000 : ℝ)^3135 := by
    have hnat : (4320519793 : ℕ)^4159*50000000000000^3135 ≤ 16423260770603^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4320519793 10000000000 16423260770603 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (632147721/1250000000 : ℝ)^4159 ≤ (5059467595363/12500000000000 : ℝ)^3135 := by
    have hnat : (632147721 : ℕ)^4159*12500000000000^3135 ≤ 5059467595363^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632147721 1250000000 5059467595363 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (923376041/2500000000 : ℝ)^4159 ≤ (26677737678123/100000000000000 : ℝ)^3135 := by
    have hnat : (923376041 : ℕ)^4159*100000000000000^3135 ≤ 26677737678123^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923376041 2500000000 26677737678123 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4320519793/10000000000 : ℝ), (632147721/1250000000 : ℝ), (923376041/2500000000 : ℝ)] ![(16423260770603/50000000000000 : ℝ), (5059467595363/12500000000000 : ℝ), (26677737678123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4320519793/10000000000 : ℝ)|^4159 ≤ (16423260770603/50000000000000 : ℝ)^3135
        have hw : |(4320519793/10000000000 : ℝ)|=(4320519793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(632147721/1250000000 : ℝ)|^4159 ≤ (5059467595363/12500000000000 : ℝ)^3135
        have hw : |(632147721/1250000000 : ℝ)|=(632147721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(923376041/2500000000 : ℝ)|^4159 ≤ (26677737678123/100000000000000 : ℝ)^3135
        have hw : |(923376041/2500000000 : ℝ)|=(923376041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (697/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2777/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4103/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (697/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (697/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (343/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (697/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (697/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (343/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (697/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (697/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (343/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (343/100000 : ℝ) ^ (8317/2048 : ℝ) ≤ (195782003/2000000000000000000 : ℝ) := by
    have hpowers : (343/100000 : ℝ)^8317 ≤ (195782003/2000000000000000000 : ℝ)^2048 := by
      have hnat : (343 : ℕ)^8317*2000000000000000000^2048 ≤ 195782003^2048*100000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        343 100000 195782003 2000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (343/100000 : ℝ)) (X := (195782003/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (697/2500 : ℝ) ^ (8317/2048 : ℝ) ≤ (279437340646395057/50000000000000000000 : ℝ) := by
    have hpowers : (697/2500 : ℝ)^8317 ≤ (279437340646395057/50000000000000000000 : ℝ)^2048 := by
      have hnat : (697 : ℕ)^8317*50000000000000000000^2048 ≤ 279437340646395057^2048*2500^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        697 2500 279437340646395057 50000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (697/2500 : ℝ)) (X := (279437340646395057/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000000000195782003/1000000000000000000 : ℝ) ≤ (10000000000482099/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (1000000000195782003/1000000000000000000 : ℝ)^2048 ≤ (10000000000482099/10000000000000000 : ℝ)^8317 := by
      have hnat : (1000000000195782003 : ℕ)^2048*10000000000000000^8317 ≤ 10000000000482099^8317*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000000000195782003 1000000000000000000 10000000000482099 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000482099/10000000000000000 : ℝ)) (X := (1000000000195782003/1000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12569859336385236283/12500000000000000000 : ℝ) ≤ (10013732985665023/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (12569859336385236283/12500000000000000000 : ℝ)^2048 ≤ (10013732985665023/10000000000000000 : ℝ)^8317 := by
      have hnat : (12569859336385236283 : ℕ)^2048*10000000000000000^8317 ≤ 10013732985665023^8317*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12569859336385236283 12500000000000000000 10013732985665023 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013732985665023/10000000000000000 : ℝ)) (X := (12569859336385236283/12500000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25279437340646395057/25000000000000000000 : ℝ) ≤ (10027465970847947/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (25279437340646395057/25000000000000000000 : ℝ)^2048 ≤ (10027465970847947/10000000000000000 : ℝ)^8317 := by
      have hnat : (25279437340646395057 : ℕ)^2048*10000000000000000^8317 ≤ 10027465970847947^8317*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25279437340646395057 25000000000000000000 10027465970847947 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10027465970847947/10000000000000000 : ℝ)) (X := (25279437340646395057/25000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(195782003/2000000000000000000 : ℝ) ≤ ((275360579185440074299/275370000000000000000 : ℝ)+2*(3433246295731/688425000000000 : ℝ)*(343/100000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (275360579185440074299/275370000000000000000 : ℝ)+2*(3433246295731/688425000000000 : ℝ)*(343/100000 : ℝ)=(10000000000482099/10000000000000000 : ℝ) by norm_num, show 1+2*(195782003/2000000000000000000 : ℝ)=(1000000000195782003/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(279437340646395057/50000000000000000000 : ℝ)+(195782003/2000000000000000000 : ℝ) ≤ ((275360579185440074299/275370000000000000000 : ℝ)+(3433246295731/688425000000000 : ℝ)*((697/2500 : ℝ)+(343/100000 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (275360579185440074299/275370000000000000000 : ℝ)+(3433246295731/688425000000000 : ℝ)*((697/2500 : ℝ)+(343/100000 : ℝ))=(10013732985665023/10000000000000000 : ℝ) by norm_num, show 1+(279437340646395057/50000000000000000000 : ℝ)+(195782003/2000000000000000000 : ℝ)=(12569859336385236283/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(279437340646395057/50000000000000000000 : ℝ) ≤ ((275360579185440074299/275370000000000000000 : ℝ)+2*(3433246295731/688425000000000 : ℝ)*(697/2500 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (275360579185440074299/275370000000000000000 : ℝ)+2*(3433246295731/688425000000000 : ℝ)*(697/2500 : ℝ)=(10027465970847947/10000000000000000 : ℝ) by norm_num, show 1+2*(279437340646395057/50000000000000000000 : ℝ)=(25279437340646395057/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (275360579185440074299/275370000000000000000 : ℝ)*(X 1 0+X 2 0)+(3433246295731/688425000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (343/100000 : ℝ)) (hi := (697/2500 : ℝ)) (c := (275360579185440074299/275370000000000000000 : ℝ)) (alpha := (3433246295731/688425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (275360579185440074299/275370000000000000000 : ℝ)*(X 0 1+X 2 1)+(3433246295731/688425000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (343/100000 : ℝ)) (hi := (697/2500 : ℝ)) (c := (275360579185440074299/275370000000000000000 : ℝ)) (alpha := (3433246295731/688425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (275360579185440074299/275370000000000000000 : ℝ)*(X 0 2+X 1 2)+(3433246295731/688425000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (343/100000 : ℝ)) (hi := (697/2500 : ℝ)) (c := (275360579185440074299/275370000000000000000 : ℝ)) (alpha := (3433246295731/688425000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-21031/100000 : ℝ)*X 0 0+(5706069411/10000000000 : ℝ)*X 0 1+(4998694259/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2710027369/5000000000 : ℝ)*X 1 0+(-310646319/1250000000 : ℝ)*X 1 1+(4998693937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5420056353/10000000000 : ℝ)*X 2 0+(4998692469/10000000000 : ℝ)*X 2 1+(-2485170311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1079719039/2500000000 : ℝ)*X 0 0+(3673845183/10000000000 : ℝ)*X 0 1+(5076456783/10000000000 : ℝ)*X 0 2+(1079719039/2500000000 : ℝ)*X 1 0+(3673845183/10000000000 : ℝ)*X 1 1+(5076456783/10000000000 : ℝ)*X 1 2+(1079719039/2500000000 : ℝ)*X 2 0+(3673845183/10000000000 : ℝ)*X 2 1+(5076456783/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2103930239/10000000000 : ℝ)*X 0 0+(1001683113/2000000000 : ℝ)*X 0 1+(5696154347/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10232133/19531250 : ℝ)*X 1 0+(-1787709769/10000000000 : ℝ)*X 1 1+(1139230821/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1047770427/2000000000 : ℝ)*X 2 0+(1424038567/2500000000 : ℝ)*X 2 1+(-71508379/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4320519793/10000000000 : ℝ)*X 0 0+(632147721/1250000000 : ℝ)*X 0 1+(923376041/2500000000 : ℝ)*X 0 2+(4320519793/10000000000 : ℝ)*X 1 0+(632147721/1250000000 : ℝ)*X 1 1+(923376041/2500000000 : ℝ)*X 1 2+(4320519793/10000000000 : ℝ)*X 2 0+(632147721/1250000000 : ℝ)*X 2 1+(923376041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11227215956591502737887547303/2294750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (349535821/100000000000000 : ℝ)*(base1) + (74085903/10000000000000 : ℝ)*(base19) + (115656251/10000000000000 : ℝ)*(base23) + (14962907/100000000000000 : ℝ)*(base24) + (27614151/25000000000000 : ℝ)*(upper5) + (531658957106599/50000000000000 : ℝ)*(major0) + (531658957106599/50000000000000 : ℝ)*(major1) + (531658957106599/50000000000000 : ℝ)*(major2) + (1413677453521991/100000000000000 : ℝ)*(sp0) + (141367851785297/10000000000000 : ℝ)*(sp1) + (706839184719321/50000000000000 : ℝ)*(sp2) + (44559735927561/6250000000000 : ℝ)*(sp3) + (2436977889/100000000000000 : ℝ)*(sp4) + (282252059/100000000000000 : ℝ)*(sp5) + (712956124376797/100000000000000 : ℝ)*(f.failure) + (706839770482029/50000000000000 : ℝ)*(f.sum) + (110286115721773/137685000000000000000000000000 : ℝ)*base66 + (26867946939918200899/13768500000000000000000000000000000 : ℝ)*base68 + (67674272257989200899/13768500000000000000000000000000000 : ℝ)*base70 + (86189909007759200899/13768500000000000000000000000000000 : ℝ)*base72 + (228469650706007/137685000000000000000000000000 : ℝ)*base73 + (70452919857499700899/13768500000000000000000000000000000 : ℝ)*base76 + (4783034579646200899/13768500000000000000000000000000000 : ℝ)*base78 + (49360547338890200899/13768500000000000000000000000000000 : ℝ)*base80 + (199408986592471/68842500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (42189/80000000000000000000 : ℝ)*base89 + (42189/80000000000000000000 : ℝ)*base91 + (42189/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (87185276253622452426897/9179000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112138133/100000000000000 : ℝ)*(base1) + (2100249021/100000000000000 : ℝ)*(base19) + (106560957/5000000000000 : ℝ)*(base23) + (104708383/50000000000000 : ℝ)*(upper3) + (215071757/100000000000000 : ℝ)*(upper5) + (21873520599153/2000000000000 : ℝ)*(major0) + (21873520599153/2000000000000 : ℝ)*(major1) + (21873520599153/2000000000000 : ℝ)*(major2) + (8537185111/100000000000000 : ℝ)*(sp1) + (91195497/1000000000000 : ℝ)*(sp2) + (1454040572692351/100000000000000 : ℝ)*(sp4) + (727014911560043/50000000000000 : ℝ)*(sp5) + (727014604892689/50000000000000 : ℝ)*(sp6) + (733311170611559/100000000000000 : ℝ)*(sp7) + (183327820687423/25000000000000 : ℝ)*(f.failure) + (727020230277109/50000000000000 : ℝ)*(f.sum) + (6249036278501/4589500000000000000000000000 : ℝ)*base66 + (771382055640103751/183580000000000000000000000000000 : ℝ)*base68 + (1241089490071216249/183580000000000000000000000000000 : ℝ)*base69 + (358656367685823751/183580000000000000000000000000000 : ℝ)*base72 + (21354455370467/4589500000000000000000000000 : ℝ)*base74 + (1142520754512016249/183580000000000000000000000000000 : ℝ)*base75 + (274342166791696249/183580000000000000000000000000000 : ℝ)*base77 + (700714639914723751/183580000000000000000000000000000 : ℝ)*base80 + (17451908039493/4589500000000000000000000000 : ℝ)*base81 + (184049/20000000000000000000 : ℝ)*base90 + (184049/20000000000000000000 : ℝ)*base92 + (184049/20000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1125_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (697/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (343/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2777/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4103/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1125_s2_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-33706941/156250000 : ℝ)*x 0 + (689259901/1250000000 : ℝ)*x 1 + (5156272847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33706941/156250000 : ℝ)^4159 ≤ (13071567551173/100000000000000 : ℝ)^3135 := by
    have hnat : (33706941 : ℕ)^4159*100000000000000^3135 ≤ 13071567551173^3135*156250000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33706941 156250000 13071567551173 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (689259901/1250000000 : ℝ)^4159 ≤ (45397202740097/100000000000000 : ℝ)^3135 := by
    have hnat : (689259901 : ℕ)^4159*100000000000000^3135 ≤ 45397202740097^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      689259901 1250000000 45397202740097 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5156272847/10000000000 : ℝ)^4159 ≤ (519140371133/1250000000000 : ℝ)^3135 := by
    have hnat : (5156272847 : ℕ)^4159*1250000000000^3135 ≤ 519140371133^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156272847 10000000000 519140371133 1250000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33706941/156250000 : ℝ), (689259901/1250000000 : ℝ), (5156272847/10000000000 : ℝ)] ![(13071567551173/100000000000000 : ℝ), (45397202740097/100000000000000 : ℝ), (519140371133/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33706941/156250000 : ℝ)|^4159 ≤ (13071567551173/100000000000000 : ℝ)^3135
        have hw : |(-33706941/156250000 : ℝ)|=(33706941/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(689259901/1250000000 : ℝ)|^4159 ≤ (45397202740097/100000000000000 : ℝ)^3135
        have hw : |(689259901/1250000000 : ℝ)|=(689259901/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5156272847/10000000000 : ℝ)|^4159 ≤ (519140371133/1250000000000 : ℝ)^3135
        have hw : |(5156272847/10000000000 : ℝ)|=(5156272847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s2_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343649963/2500000000 : ℝ)*x 0 + (-468678573/2000000000 : ℝ)*x 1 + (5156274433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343649963/2500000000 : ℝ)^4159 ≤ (21940060085677/50000000000000 : ℝ)^3135 := by
    have hnat : (1343649963 : ℕ)^4159*50000000000000^3135 ≤ 21940060085677^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343649963 2500000000 21940060085677 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (468678573/2000000000 : ℝ)^4159 ≤ (113973696691/781250000000 : ℝ)^3135 := by
    have hnat : (468678573 : ℕ)^4159*781250000000^3135 ≤ 113973696691^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      468678573 2000000000 113973696691 781250000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5156274433/10000000000 : ℝ)^4159 ≤ (8306249327533/20000000000000 : ℝ)^3135 := by
    have hnat : (5156274433 : ℕ)^4159*20000000000000^3135 ≤ 8306249327533^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156274433 10000000000 8306249327533 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343649963/2500000000 : ℝ), (-468678573/2000000000 : ℝ), (5156274433/10000000000 : ℝ)] ![(21940060085677/50000000000000 : ℝ), (113973696691/781250000000 : ℝ), (8306249327533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343649963/2500000000 : ℝ)|^4159 ≤ (21940060085677/50000000000000 : ℝ)^3135
        have hw : |(1343649963/2500000000 : ℝ)|=(1343649963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-468678573/2000000000 : ℝ)|^4159 ≤ (113973696691/781250000000 : ℝ)^3135
        have hw : |(-468678573/2000000000 : ℝ)|=(468678573/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5156274433/10000000000 : ℝ)|^4159 ≤ (8306249327533/20000000000000 : ℝ)^3135
        have hw : |(5156274433/10000000000 : ℝ)|=(5156274433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s2_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687299887/5000000000 : ℝ)*x 0 + (5156274473/10000000000 : ℝ)*x 1 + (-585848229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687299887/5000000000 : ℝ)^4159 ≤ (43880119326527/100000000000000 : ℝ)^3135 := by
    have hnat : (2687299887 : ℕ)^4159*100000000000000^3135 ≤ 43880119326527^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687299887 5000000000 43880119326527 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5156274473/10000000000 : ℝ)^4159 ≤ (41531247065081/100000000000000 : ℝ)^3135 := by
    have hnat : (5156274473 : ℕ)^4159*100000000000000^3135 ≤ 41531247065081^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5156274473 10000000000 41531247065081 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (585848229/2500000000 : ℝ)^4159 ≤ (14588633597651/100000000000000 : ℝ)^3135 := by
    have hnat : (585848229 : ℕ)^4159*100000000000000^3135 ≤ 14588633597651^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585848229 2500000000 14588633597651 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687299887/5000000000 : ℝ), (5156274473/10000000000 : ℝ), (-585848229/2500000000 : ℝ)] ![(43880119326527/100000000000000 : ℝ), (41531247065081/100000000000000 : ℝ), (14588633597651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687299887/5000000000 : ℝ)|^4159 ≤ (43880119326527/100000000000000 : ℝ)^3135
        have hw : |(2687299887/5000000000 : ℝ)|=(2687299887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5156274473/10000000000 : ℝ)|^4159 ≤ (41531247065081/100000000000000 : ℝ)^3135
        have hw : |(5156274473/10000000000 : ℝ)|=(5156274473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-585848229/2500000000 : ℝ)|^4159 ≤ (14588633597651/100000000000000 : ℝ)^3135
        have hw : |(-585848229/2500000000 : ℝ)|=(585848229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s2_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4355980331/10000000000 : ℝ)*x 0 + (2007807889/5000000000 : ℝ)*x 1 + (4725085549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355980331/10000000000 : ℝ)^4159 ≤ (6640928668767/20000000000000 : ℝ)^3135 := by
    have hnat : (4355980331 : ℕ)^4159*20000000000000^3135 ≤ 6640928668767^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355980331 10000000000 6640928668767 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007807889/5000000000 : ℝ)^4159 ≤ (14903690808067/50000000000000 : ℝ)^3135 := by
    have hnat : (2007807889 : ℕ)^4159*50000000000000^3135 ≤ 14903690808067^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007807889 5000000000 14903690808067 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4725085549/10000000000 : ℝ)^4159 ≤ (3698797502703/10000000000000 : ℝ)^3135 := by
    have hnat : (4725085549 : ℕ)^4159*10000000000000^3135 ≤ 3698797502703^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4725085549 10000000000 3698797502703 10000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355980331/10000000000 : ℝ), (2007807889/5000000000 : ℝ), (4725085549/10000000000 : ℝ)] ![(6640928668767/20000000000000 : ℝ), (14903690808067/50000000000000 : ℝ), (3698797502703/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355980331/10000000000 : ℝ)|^4159 ≤ (6640928668767/20000000000000 : ℝ)^3135
        have hw : |(4355980331/10000000000 : ℝ)|=(4355980331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007807889/5000000000 : ℝ)|^4159 ≤ (14903690808067/50000000000000 : ℝ)^3135
        have hw : |(2007807889/5000000000 : ℝ)|=(2007807889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4725085549/10000000000 : ℝ)|^4159 ≤ (3698797502703/10000000000000 : ℝ)^3135
        have hw : |(4725085549/10000000000 : ℝ)|=(4725085549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s2_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2157351667/10000000000 : ℝ)*x 0 + (5158769893/10000000000 : ℝ)*x 1 + (1377889207/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157351667/10000000000 : ℝ)^4159 ≤ (3268107812033/25000000000000 : ℝ)^3135 := by
    have hnat : (2157351667 : ℕ)^4159*25000000000000^3135 ≤ 3268107812033^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157351667 10000000000 3268107812033 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5158769893/10000000000 : ℝ)^4159 ≤ (20778956852371/50000000000000 : ℝ)^3135 := by
    have hnat : (5158769893 : ℕ)^4159*50000000000000^3135 ≤ 20778956852371^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5158769893 10000000000 20778956852371 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1377889207/2500000000 : ℝ)^4159 ≤ (45369655028181/100000000000000 : ℝ)^3135 := by
    have hnat : (1377889207 : ℕ)^4159*100000000000000^3135 ≤ 45369655028181^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377889207 2500000000 45369655028181 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2157351667/10000000000 : ℝ), (5158769893/10000000000 : ℝ), (1377889207/2500000000 : ℝ)] ![(3268107812033/25000000000000 : ℝ), (20778956852371/50000000000000 : ℝ), (45369655028181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2157351667/10000000000 : ℝ)|^4159 ≤ (3268107812033/25000000000000 : ℝ)^3135
        have hw : |(-2157351667/10000000000 : ℝ)|=(2157351667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5158769893/10000000000 : ℝ)|^4159 ≤ (20778956852371/50000000000000 : ℝ)^3135
        have hw : |(5158769893/10000000000 : ℝ)|=(5158769893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1377889207/2500000000 : ℝ)|^4159 ≤ (45369655028181/100000000000000 : ℝ)^3135
        have hw : |(1377889207/2500000000 : ℝ)|=(1377889207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s2_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1320979583/2500000000 : ℝ)*x 0 + (-1988108797/10000000000 : ℝ)*x 1 + (5511557367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320979583/2500000000 : ℝ)^4159 ≤ (42900655222927/100000000000000 : ℝ)^3135 := by
    have hnat : (1320979583 : ℕ)^4159*100000000000000^3135 ≤ 42900655222927^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320979583 2500000000 42900655222927 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1988108797/10000000000 : ℝ)^4159 ≤ (183276310113/1562500000000 : ℝ)^3135 := by
    have hnat : (1988108797 : ℕ)^4159*1562500000000^3135 ≤ 183276310113^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988108797 10000000000 183276310113 1562500000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5511557367/10000000000 : ℝ)^4159 ≤ (45369660914331/100000000000000 : ℝ)^3135 := by
    have hnat : (5511557367 : ℕ)^4159*100000000000000^3135 ≤ 45369660914331^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511557367 10000000000 45369660914331 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320979583/2500000000 : ℝ), (-1988108797/10000000000 : ℝ), (5511557367/10000000000 : ℝ)] ![(42900655222927/100000000000000 : ℝ), (183276310113/1562500000000 : ℝ), (45369660914331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320979583/2500000000 : ℝ)|^4159 ≤ (42900655222927/100000000000000 : ℝ)^3135
        have hw : |(1320979583/2500000000 : ℝ)|=(1320979583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1988108797/10000000000 : ℝ)|^4159 ≤ (183276310113/1562500000000 : ℝ)^3135
        have hw : |(-1988108797/10000000000 : ℝ)|=(1988108797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5511557367/10000000000 : ℝ)|^4159 ≤ (45369660914331/100000000000000 : ℝ)^3135
        have hw : |(5511557367/10000000000 : ℝ)|=(5511557367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s2_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1320979281/2500000000 : ℝ)*x 0 + (5511557249/10000000000 : ℝ)*x 1 + (-62128457/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320979281/2500000000 : ℝ)^4159 ≤ (5362580276433/12500000000000 : ℝ)^3135 := by
    have hnat : (1320979281 : ℕ)^4159*12500000000000^3135 ≤ 5362580276433^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320979281 2500000000 5362580276433 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511557249/10000000000 : ℝ)^4159 ≤ (2835603726607/6250000000000 : ℝ)^3135 := by
    have hnat : (5511557249 : ℕ)^4159*6250000000000^3135 ≤ 2835603726607^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511557249 10000000000 2835603726607 6250000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62128457/312500000 : ℝ)^4159 ≤ (2932424536809/25000000000000 : ℝ)^3135 := by
    have hnat : (62128457 : ℕ)^4159*25000000000000^3135 ≤ 2932424536809^3135*312500000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62128457 312500000 2932424536809 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320979281/2500000000 : ℝ), (5511557249/10000000000 : ℝ), (-62128457/312500000 : ℝ)] ![(5362580276433/12500000000000 : ℝ), (2835603726607/6250000000000 : ℝ), (2932424536809/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320979281/2500000000 : ℝ)|^4159 ≤ (5362580276433/12500000000000 : ℝ)^3135
        have hw : |(1320979281/2500000000 : ℝ)|=(1320979281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511557249/10000000000 : ℝ)|^4159 ≤ (2835603726607/6250000000000 : ℝ)^3135
        have hw : |(5511557249/10000000000 : ℝ)|=(5511557249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62128457/312500000 : ℝ)|^4159 ≤ (2932424536809/25000000000000 : ℝ)^3135
        have hw : |(-62128457/312500000 : ℝ)|=(62128457/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s2_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544524117/1250000000 : ℝ)*x 0 + (4720135539/10000000000 : ℝ)*x 1 + (4020615713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544524117/1250000000 : ℝ)^4159 ≤ (16603396678751/50000000000000 : ℝ)^3135 := by
    have hnat : (544524117 : ℕ)^4159*50000000000000^3135 ≤ 16603396678751^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544524117 1250000000 16603396678751 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4720135539/10000000000 : ℝ)^4159 ≤ (18468289236421/50000000000000 : ℝ)^3135 := by
    have hnat : (4720135539 : ℕ)^4159*50000000000000^3135 ≤ 18468289236421^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4720135539 10000000000 18468289236421 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4020615713/10000000000 : ℝ)^4159 ≤ (14928314076183/50000000000000 : ℝ)^3135 := by
    have hnat : (4020615713 : ℕ)^4159*50000000000000^3135 ≤ 14928314076183^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4020615713 10000000000 14928314076183 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544524117/1250000000 : ℝ), (4720135539/10000000000 : ℝ), (4020615713/10000000000 : ℝ)] ![(16603396678751/50000000000000 : ℝ), (18468289236421/50000000000000 : ℝ), (14928314076183/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544524117/1250000000 : ℝ)|^4159 ≤ (16603396678751/50000000000000 : ℝ)^3135
        have hw : |(544524117/1250000000 : ℝ)|=(544524117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4720135539/10000000000 : ℝ)|^4159 ≤ (18468289236421/50000000000000 : ℝ)^3135
        have hw : |(4720135539/10000000000 : ℝ)|=(4720135539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4020615713/10000000000 : ℝ)|^4159 ≤ (14928314076183/50000000000000 : ℝ)^3135
        have hw : |(4020615713/10000000000 : ℝ)|=(4020615713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4103/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (281/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8277/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4103/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2777/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4103/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2777/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4103/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2777/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4103/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2777/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4103/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2777/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4103/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2777/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2777/50000 : ℝ) ^ (8317/2048 : ℝ) ≤ (797627878832721/100000000000000000000 : ℝ) := by
    have hpowers : (2777/50000 : ℝ)^8317 ≤ (797627878832721/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2777 : ℕ)^8317*100000000000000000000^2048 ≤ 797627878832721^2048*50000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2777 50000 797627878832721 100000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2777/50000 : ℝ)) (X := (797627878832721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4103/20000 : ℝ) ^ (8317/2048 : ℝ) ≤ (10050282754663329/6250000000000000000 : ℝ) := by
    have hpowers : (4103/20000 : ℝ)^8317 ≤ (10050282754663329/6250000000000000000 : ℝ)^2048 := by
      have hnat : (4103 : ℕ)^8317*6250000000000000000^2048 ≤ 10050282754663329^2048*20000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4103 20000 10050282754663329 6250000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4103/20000 : ℝ)) (X := (10050282754663329/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000797627878832721/50000000000000000000 : ℝ) ≤ (10000039281762049/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50000797627878832721/50000000000000000000 : ℝ)^2048 ≤ (10000039281762049/10000000000000000 : ℝ)^8317 := by
      have hnat : (50000797627878832721 : ℕ)^2048*10000000000000000^8317 ≤ 10000039281762049^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000797627878832721 50000000000000000000 10000039281762049 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000039281762049/10000000000000000 : ℝ)) (X := (50000797627878832721/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20032320430390689197/20000000000000000000 : ℝ) ≤ (10003976912678313/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (20032320430390689197/20000000000000000000 : ℝ)^2048 ≤ (10003976912678313/10000000000000000 : ℝ)^8317 := by
      have hnat : (20032320430390689197 : ℕ)^2048*10000000000000000^8317 ≤ 10003976912678313^8317*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20032320430390689197 20000000000000000000 10003976912678313 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003976912678313/10000000000000000 : ℝ)) (X := (20032320430390689197/20000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3135050282754663329/3125000000000000000 : ℝ) ≤ (10007914543594577/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (3135050282754663329/3125000000000000000 : ℝ)^2048 ≤ (10007914543594577/10000000000000000 : ℝ)^8317 := by
      have hnat : (3135050282754663329 : ℕ)^2048*10000000000000000^8317 ≤ 10007914543594577^8317*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3135050282754663329 3125000000000000000 10007914543594577 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007914543594577/10000000000000000 : ℝ)) (X := (3135050282754663329/3125000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(797627878832721/100000000000000000000 : ℝ) ≤ ((149566848490224154577/149610000000000000000 : ℝ)+2*(492203864533/187012500000000 : ℝ)*(2777/50000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (149566848490224154577/149610000000000000000 : ℝ)+2*(492203864533/187012500000000 : ℝ)*(2777/50000 : ℝ)=(10000039281762049/10000000000000000 : ℝ) by norm_num, show 1+2*(797627878832721/100000000000000000000 : ℝ)=(50000797627878832721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10050282754663329/6250000000000000000 : ℝ)+(797627878832721/100000000000000000000 : ℝ) ≤ ((149566848490224154577/149610000000000000000 : ℝ)+(492203864533/187012500000000 : ℝ)*((4103/20000 : ℝ)+(2777/50000 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (149566848490224154577/149610000000000000000 : ℝ)+(492203864533/187012500000000 : ℝ)*((4103/20000 : ℝ)+(2777/50000 : ℝ))=(10003976912678313/10000000000000000 : ℝ) by norm_num, show 1+(10050282754663329/6250000000000000000 : ℝ)+(797627878832721/100000000000000000000 : ℝ)=(20032320430390689197/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10050282754663329/6250000000000000000 : ℝ) ≤ ((149566848490224154577/149610000000000000000 : ℝ)+2*(492203864533/187012500000000 : ℝ)*(4103/20000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (149566848490224154577/149610000000000000000 : ℝ)+2*(492203864533/187012500000000 : ℝ)*(4103/20000 : ℝ)=(10007914543594577/10000000000000000 : ℝ) by norm_num, show 1+2*(10050282754663329/6250000000000000000 : ℝ)=(3135050282754663329/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (149566848490224154577/149610000000000000000 : ℝ)*(X 1 0+X 2 0)+(492203864533/187012500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (2777/50000 : ℝ)) (hi := (4103/20000 : ℝ)) (c := (149566848490224154577/149610000000000000000 : ℝ)) (alpha := (492203864533/187012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (149566848490224154577/149610000000000000000 : ℝ)*(X 0 1+X 2 1)+(492203864533/187012500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (2777/50000 : ℝ)) (hi := (4103/20000 : ℝ)) (c := (149566848490224154577/149610000000000000000 : ℝ)) (alpha := (492203864533/187012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (149566848490224154577/149610000000000000000 : ℝ)*(X 0 2+X 1 2)+(492203864533/187012500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (2777/50000 : ℝ)) (hi := (4103/20000 : ℝ)) (c := (149566848490224154577/149610000000000000000 : ℝ)) (alpha := (492203864533/187012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-33706941/156250000 : ℝ)*X 0 0+(689259901/1250000000 : ℝ)*X 0 1+(5156272847/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1343649963/2500000000 : ℝ)*X 1 0+(-468678573/2000000000 : ℝ)*X 1 1+(5156274433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2687299887/5000000000 : ℝ)*X 2 0+(5156274473/10000000000 : ℝ)*X 2 1+(-585848229/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355980331/10000000000 : ℝ)*X 0 0+(2007807889/5000000000 : ℝ)*X 0 1+(4725085549/10000000000 : ℝ)*X 0 2+(4355980331/10000000000 : ℝ)*X 1 0+(2007807889/5000000000 : ℝ)*X 1 1+(4725085549/10000000000 : ℝ)*X 1 2+(4355980331/10000000000 : ℝ)*X 2 0+(2007807889/5000000000 : ℝ)*X 2 1+(4725085549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2157351667/10000000000 : ℝ)*X 0 0+(5158769893/10000000000 : ℝ)*X 0 1+(1377889207/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320979583/2500000000 : ℝ)*X 1 0+(-1988108797/10000000000 : ℝ)*X 1 1+(5511557367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1320979281/2500000000 : ℝ)*X 2 0+(5511557249/10000000000 : ℝ)*X 2 1+(-62128457/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((544524117/1250000000 : ℝ)*X 0 0+(4720135539/10000000000 : ℝ)*X 0 1+(4020615713/10000000000 : ℝ)*X 0 2+(544524117/1250000000 : ℝ)*X 1 0+(4720135539/10000000000 : ℝ)*X 1 1+(4020615713/10000000000 : ℝ)*X 1 2+(544524117/1250000000 : ℝ)*X 2 0+(4720135539/10000000000 : ℝ)*X 2 1+(4020615713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (300313057327540297268537/24935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158745609/10000000000000 : ℝ)*(base19) + (652736319/50000000000000 : ℝ)*(base23) + (40456603/12500000000000 : ℝ)*(upper3) + (64877461/50000000000000 : ℝ)*(upper4) + (12287771/12500000000000 : ℝ)*(upper5) + (2102191448010493/100000000000000 : ℝ)*(major0) + (2102191448010493/100000000000000 : ℝ)*(major1) + (2102191448010493/100000000000000 : ℝ)*(major2) + (139741761371791/5000000000000 : ℝ)*(sp0) + (1397429324524581/50000000000000 : ℝ)*(sp1) + (558971786206523/20000000000000 : ℝ)*(sp2) + (704755847294833/50000000000000 : ℝ)*(sp3) + (25009069433/100000000000000 : ℝ)*(sp4) + (10563464853/100000000000000 : ℝ)*(sp7) + (1409522258054519/100000000000000 : ℝ)*(f.failure) + (698715059126313/25000000000000 : ℝ)*(f.sum) + (29732033308937/74805000000000000000000000000 : ℝ)*base65 + (15963843731018823539/14961000000000000000000000000000000 : ℝ)*base68 + (1067441484041823539/14961000000000000000000000000000000 : ℝ)*base70 + (70433092658607176461/14961000000000000000000000000000000 : ℝ)*base71 + (439691216318773/74805000000000000000000000000 : ℝ)*base74 + (144020490312156176461/14961000000000000000000000000000000 : ℝ)*base75 + (51345033636938823539/14961000000000000000000000000000000 : ℝ)*base78 + (116717400779955176461/14961000000000000000000000000000000 : ℝ)*base79 + (369178878652663/74805000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (236103/80000000000000000000 : ℝ)*base89 + (236103/80000000000000000000 : ℝ)*base91 + (236103/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21864061938156968841687/2493500000000000000000000000 : ℝ) := by norm_num
    linear_combination (158495769/10000000000000 : ℝ)*(base19) + (275207487/25000000000000 : ℝ)*(base23) + (43776667/20000000000000 : ℝ)*(upper2) + (96125127/100000000000000 : ℝ)*(upper3) + (63891907/25000000000000 : ℝ)*(upper5) + (85282354368337/4000000000000 : ℝ)*(major0) + (85282354368337/4000000000000 : ℝ)*(major1) + (85282354368337/4000000000000 : ℝ)*(major2) + (5404546887/25000000000000 : ℝ)*(sp1) + (439446913/6250000000000 : ℝ)*(sp2) + (1417284513891111/50000000000000 : ℝ)*(sp4) + (354318228079623/12500000000000 : ℝ)*(sp5) + (1417280447900833/50000000000000 : ℝ)*(sp6) + (1429548398353869/100000000000000 : ℝ)*(sp7) + (1429548398353869/100000000000000 : ℝ)*(f.failure) + (1417284513891111/50000000000000 : ℝ)*(f.sum) + (185314517807/1496100000000000000000000000 : ℝ)*base66 + (1682887156292948449/598440000000000000000000000000000 : ℝ)*base67 + (572371551376491551/598440000000000000000000000000000 : ℝ)*base70 + (3255820669809308449/598440000000000000000000000000000 : ℝ)*base71 + (39355162952363/14961000000000000000000000000 : ℝ)*base74 + (2640645778006731551/598440000000000000000000000000000 : ℝ)*base76 + (1777094195547171551/598440000000000000000000000000000 : ℝ)*base78 + (5068163989201268449/598440000000000000000000000000000 : ℝ)*base79 + (4938359303569/2992200000000000000000000000 : ℝ)*base82 + (197053/80000000000000000000 : ℝ)*base89 + (197053/80000000000000000000 : ℝ)*base91 + (197053/80000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1125_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4103/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8277/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1125_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8277/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1125_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1125_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1125_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8277/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1125_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
