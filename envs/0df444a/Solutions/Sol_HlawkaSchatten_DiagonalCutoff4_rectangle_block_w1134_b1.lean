-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1134_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:28:27.137014+00:00
-- url     : https://prove2.me/submissions/9bfae671-fd4f-4a5b-a791-512e4fa324e3

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
theorem support_rectangle_w1134_s3_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-541705881/2500000000 : ℝ)*x 0 + (543001629/1000000000 : ℝ)*x 1 + (5231320399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541705881/2500000000 : ℝ)^8327 ≤ (2631609036063/20000000000000 : ℝ)^6279 := by
    have hnat : (541705881 : ℕ)^8327*20000000000000^6279 ≤ 2631609036063^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541705881 2500000000 2631609036063 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543001629/1000000000 : ℝ)^8327 ≤ (44494068897347/100000000000000 : ℝ)^6279 := by
    have hnat : (543001629 : ℕ)^8327*100000000000000^6279 ≤ 44494068897347^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543001629 1000000000 44494068897347 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5231320399/10000000000 : ℝ)^8327 ≤ (10586971476011/25000000000000 : ℝ)^6279 := by
    have hnat : (5231320399 : ℕ)^8327*25000000000000^6279 ≤ 10586971476011^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231320399 10000000000 10586971476011 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541705881/2500000000 : ℝ), (543001629/1000000000 : ℝ), (5231320399/10000000000 : ℝ)] ![(2631609036063/20000000000000 : ℝ), (44494068897347/100000000000000 : ℝ), (10586971476011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541705881/2500000000 : ℝ)|^8327 ≤ (2631609036063/20000000000000 : ℝ)^6279
        have hw : |(-541705881/2500000000 : ℝ)|=(541705881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543001629/1000000000 : ℝ)|^8327 ≤ (44494068897347/100000000000000 : ℝ)^6279
        have hw : |(543001629/1000000000 : ℝ)|=(543001629/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5231320399/10000000000 : ℝ)|^8327 ≤ (10586971476011/25000000000000 : ℝ)^6279
        have hw : |(5231320399/10000000000 : ℝ)|=(5231320399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s3_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (669248747/1250000000 : ℝ)*x 0 + (-283551023/1250000000 : ℝ)*x 1 + (2615660133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669248747/1250000000 : ℝ)^8327 ≤ (43669803472051/100000000000000 : ℝ)^6279 := by
    have hnat : (669248747 : ℕ)^8327*100000000000000^6279 ≤ 43669803472051^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669248747 1250000000 43669803472051 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (283551023/1250000000 : ℝ)^8327 ≤ (13982312040337/100000000000000 : ℝ)^6279 := by
    have hnat : (283551023 : ℕ)^8327*100000000000000^6279 ≤ 13982312040337^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283551023 1250000000 13982312040337 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2615660133/5000000000 : ℝ)^8327 ≤ (8469576895247/20000000000000 : ℝ)^6279 := by
    have hnat : (2615660133 : ℕ)^8327*20000000000000^6279 ≤ 8469576895247^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615660133 5000000000 8469576895247 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669248747/1250000000 : ℝ), (-283551023/1250000000 : ℝ), (2615660133/5000000000 : ℝ)] ![(43669803472051/100000000000000 : ℝ), (13982312040337/100000000000000 : ℝ), (8469576895247/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669248747/1250000000 : ℝ)|^8327 ≤ (43669803472051/100000000000000 : ℝ)^6279
        have hw : |(669248747/1250000000 : ℝ)|=(669248747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-283551023/1250000000 : ℝ)|^8327 ≤ (13982312040337/100000000000000 : ℝ)^6279
        have hw : |(-283551023/1250000000 : ℝ)|=(283551023/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2615660133/5000000000 : ℝ)|^8327 ≤ (8469576895247/20000000000000 : ℝ)^6279
        have hw : |(2615660133/5000000000 : ℝ)|=(2615660133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s3_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5353990063/10000000000 : ℝ)*x 0 + (2615660179/5000000000 : ℝ)*x 1 + (-1134203973/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353990063/10000000000 : ℝ)^8327 ≤ (43669804413119/100000000000000 : ℝ)^6279 := by
    have hnat : (5353990063 : ℕ)^8327*100000000000000^6279 ≤ 43669804413119^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353990063 10000000000 43669804413119 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615660179/5000000000 : ℝ)^8327 ≤ (10586971365973/25000000000000 : ℝ)^6279 := by
    have hnat : (2615660179 : ℕ)^8327*25000000000000^6279 ≤ 10586971365973^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615660179 5000000000 10586971365973 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134203973/5000000000 : ℝ)^8327 ≤ (1398231009483/10000000000000 : ℝ)^6279 := by
    have hnat : (1134203973 : ℕ)^8327*10000000000000^6279 ≤ 1398231009483^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134203973 5000000000 1398231009483 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353990063/10000000000 : ℝ), (2615660179/5000000000 : ℝ), (-1134203973/5000000000 : ℝ)] ![(43669804413119/100000000000000 : ℝ), (10586971365973/25000000000000 : ℝ), (1398231009483/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353990063/10000000000 : ℝ)|^8327 ≤ (43669804413119/100000000000000 : ℝ)^6279
        have hw : |(5353990063/10000000000 : ℝ)|=(5353990063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615660179/5000000000 : ℝ)|^8327 ≤ (10586971365973/25000000000000 : ℝ)^6279
        have hw : |(2615660179/5000000000 : ℝ)|=(2615660179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1134203973/5000000000 : ℝ)|^8327 ≤ (1398231009483/10000000000000 : ℝ)^6279
        have hw : |(-1134203973/5000000000 : ℝ)|=(1134203973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s3_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2181745729/5000000000 : ℝ)*x 0 + (1042648529/2500000000 : ℝ)*x 1 + (285329619/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2181745729/5000000000 : ℝ)^8327 ≤ (33293546345243/100000000000000 : ℝ)^6279 := by
    have hnat : (2181745729 : ℕ)^8327*100000000000000^6279 ≤ 33293546345243^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181745729 5000000000 33293546345243 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042648529/2500000000 : ℝ)^8327 ≤ (15677946725087/50000000000000 : ℝ)^6279 := by
    have hnat : (1042648529 : ℕ)^8327*50000000000000^6279 ≤ 15677946725087^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042648529 2500000000 15677946725087 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285329619/625000000 : ℝ)^8327 ≤ (7070112037379/20000000000000 : ℝ)^6279 := by
    have hnat : (285329619 : ℕ)^8327*20000000000000^6279 ≤ 7070112037379^6279*625000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285329619 625000000 7070112037379 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2181745729/5000000000 : ℝ), (1042648529/2500000000 : ℝ), (285329619/625000000 : ℝ)] ![(33293546345243/100000000000000 : ℝ), (15677946725087/50000000000000 : ℝ), (7070112037379/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2181745729/5000000000 : ℝ)|^8327 ≤ (33293546345243/100000000000000 : ℝ)^6279
        have hw : |(2181745729/5000000000 : ℝ)|=(2181745729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1042648529/2500000000 : ℝ)|^8327 ≤ (15677946725087/50000000000000 : ℝ)^6279
        have hw : |(1042648529/2500000000 : ℝ)|=(1042648529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285329619/625000000 : ℝ)|^8327 ≤ (7070112037379/20000000000000 : ℝ)^6279
        have hw : |(285329619/625000000 : ℝ)|=(285329619/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s3_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1083420999/5000000000 : ℝ)*x 0 + (523209553/1000000000 : ℝ)*x 1 + (3393273/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083420999/5000000000 : ℝ)^8327 ≤ (6579096977229/50000000000000 : ℝ)^6279 := by
    have hnat : (1083420999 : ℕ)^8327*50000000000000^6279 ≤ 6579096977229^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083420999 5000000000 6579096977229 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523209553/1000000000 : ℝ)^8327 ≤ (42356207451537/100000000000000 : ℝ)^6279 := by
    have hnat : (523209553 : ℕ)^8327*100000000000000^6279 ≤ 42356207451537^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523209553 1000000000 42356207451537 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3393273/6250000 : ℝ)^8327 ≤ (22242799292237/50000000000000 : ℝ)^6279 := by
    have hnat : (3393273 : ℕ)^8327*50000000000000^6279 ≤ 22242799292237^6279*6250000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3393273 6250000 22242799292237 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1083420999/5000000000 : ℝ), (523209553/1000000000 : ℝ), (3393273/6250000 : ℝ)] ![(6579096977229/50000000000000 : ℝ), (42356207451537/100000000000000 : ℝ), (22242799292237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1083420999/5000000000 : ℝ)|^8327 ≤ (6579096977229/50000000000000 : ℝ)^6279
        have hw : |(-1083420999/5000000000 : ℝ)|=(1083420999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523209553/1000000000 : ℝ)|^8327 ≤ (42356207451537/100000000000000 : ℝ)^6279
        have hw : |(523209553/1000000000 : ℝ)|=(523209553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3393273/6250000 : ℝ)|^8327 ≤ (22242799292237/50000000000000 : ℝ)^6279
        have hw : |(3393273/6250000 : ℝ)|=(3393273/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s3_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (530368057/1000000000 : ℝ)*x 0 + (-1035246081/5000000000 : ℝ)*x 1 + (1085847303/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530368057/1000000000 : ℝ)^8327 ≤ (10781612168769/25000000000000 : ℝ)^6279 := by
    have hnat : (530368057 : ℕ)^8327*25000000000000^6279 ≤ 10781612168769^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530368057 1000000000 10781612168769 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035246081/5000000000 : ℝ)^8327 ≤ (12387955827913/100000000000000 : ℝ)^6279 := by
    have hnat : (1035246081 : ℕ)^8327*100000000000000^6279 ≤ 12387955827913^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035246081 5000000000 12387955827913 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085847303/2000000000 : ℝ)^8327 ≤ (111213988719/250000000000 : ℝ)^6279 := by
    have hnat : (1085847303 : ℕ)^8327*250000000000^6279 ≤ 111213988719^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085847303 2000000000 111213988719 250000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530368057/1000000000 : ℝ), (-1035246081/5000000000 : ℝ), (1085847303/2000000000 : ℝ)] ![(10781612168769/25000000000000 : ℝ), (12387955827913/100000000000000 : ℝ), (111213988719/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530368057/1000000000 : ℝ)|^8327 ≤ (10781612168769/25000000000000 : ℝ)^6279
        have hw : |(530368057/1000000000 : ℝ)|=(530368057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035246081/5000000000 : ℝ)|^8327 ≤ (12387955827913/100000000000000 : ℝ)^6279
        have hw : |(-1035246081/5000000000 : ℝ)|=(1035246081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085847303/2000000000 : ℝ)|^8327 ≤ (111213988719/250000000000 : ℝ)^6279
        have hw : |(1085847303/2000000000 : ℝ)|=(1085847303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s3_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060736247/2000000000 : ℝ)*x 0 + (2714618023/5000000000 : ℝ)*x 1 + (-20704919/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060736247/2000000000 : ℝ)^8327 ≤ (43126455846181/100000000000000 : ℝ)^6279 := by
    have hnat : (1060736247 : ℕ)^8327*100000000000000^6279 ≤ 43126455846181^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060736247 2000000000 43126455846181 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714618023/5000000000 : ℝ)^8327 ≤ (2224279519567/5000000000000 : ℝ)^6279 := by
    have hnat : (2714618023 : ℕ)^8327*5000000000000^6279 ≤ 2224279519567^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714618023 5000000000 2224279519567 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (20704919/100000000 : ℝ)^8327 ≤ (3096988437263/25000000000000 : ℝ)^6279 := by
    have hnat : (20704919 : ℕ)^8327*25000000000000^6279 ≤ 3096988437263^6279*100000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20704919 100000000 3096988437263 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060736247/2000000000 : ℝ), (2714618023/5000000000 : ℝ), (-20704919/100000000 : ℝ)] ![(43126455846181/100000000000000 : ℝ), (2224279519567/5000000000000 : ℝ), (3096988437263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060736247/2000000000 : ℝ)|^8327 ≤ (43126455846181/100000000000000 : ℝ)^6279
        have hw : |(1060736247/2000000000 : ℝ)|=(1060736247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714618023/5000000000 : ℝ)|^8327 ≤ (2224279519567/5000000000000 : ℝ)^6279
        have hw : |(2714618023/5000000000 : ℝ)|=(2714618023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-20704919/100000000 : ℝ)|^8327 ≤ (3096988437263/25000000000000 : ℝ)^6279
        have hw : |(-20704919/100000000 : ℝ)|=(20704919/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s3_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (872705579/2000000000 : ℝ)*x 0 + (2281867141/5000000000 : ℝ)*x 1 + (2086071331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (872705579/2000000000 : ℝ)^8327 ≤ (16646957520107/50000000000000 : ℝ)^6279 := by
    have hnat : (872705579 : ℕ)^8327*50000000000000^6279 ≤ 16646957520107^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872705579 2000000000 16646957520107 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2281867141/5000000000 : ℝ)^8327 ≤ (1104210959389/3125000000000 : ℝ)^6279 := by
    have hnat : (2281867141 : ℕ)^8327*3125000000000^6279 ≤ 1104210959389^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281867141 5000000000 1104210959389 3125000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086071331/5000000000 : ℝ)^8327 ≤ (31371334248157/100000000000000 : ℝ)^6279 := by
    have hnat : (2086071331 : ℕ)^8327*100000000000000^6279 ≤ 31371334248157^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086071331 5000000000 31371334248157 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(872705579/2000000000 : ℝ), (2281867141/5000000000 : ℝ), (2086071331/5000000000 : ℝ)] ![(16646957520107/50000000000000 : ℝ), (1104210959389/3125000000000 : ℝ), (31371334248157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(872705579/2000000000 : ℝ)|^8327 ≤ (16646957520107/50000000000000 : ℝ)^6279
        have hw : |(872705579/2000000000 : ℝ)|=(872705579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2281867141/5000000000 : ℝ)|^8327 ≤ (1104210959389/3125000000000 : ℝ)^6279
        have hw : |(2281867141/5000000000 : ℝ)|=(2281867141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086071331/5000000000 : ℝ)|^8327 ≤ (31371334248157/100000000000000 : ℝ)^6279
        have hw : |(2086071331/5000000000 : ℝ)|=(2086071331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10611/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2963/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16527/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4517/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16527/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4517/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16527/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4517/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16527/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4517/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16527/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4517/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16527/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4517/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4517/50000 : ℝ) ^ (4163/1024 : ℝ) ≤ (1138240150410511/20000000000000000000 : ℝ) := by
    have hpowers : (4517/50000 : ℝ)^4163 ≤ (1138240150410511/20000000000000000000 : ℝ)^1024 := by
      have hnat : (4517 : ℕ)^4163*20000000000000000000^1024 ≤ 1138240150410511^1024*50000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4517 50000 1138240150410511 20000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4517/50000 : ℝ)) (X := (1138240150410511/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16527/100000 : ℝ) ^ (4163/1024 : ℝ) ≤ (8289585225212119/12500000000000000000 : ℝ) := by
    have hpowers : (16527/100000 : ℝ)^4163 ≤ (8289585225212119/12500000000000000000 : ℝ)^1024 := by
      have hnat : (16527 : ℕ)^4163*12500000000000000000^1024 ≤ 8289585225212119^1024*100000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16527 100000 8289585225212119 12500000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16527/100000 : ℝ)) (X := (8289585225212119/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001138240150410511/10000000000000000000 : ℝ) ≤ (10000279968268021/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (10001138240150410511/10000000000000000000 : ℝ)^1024 ≤ (10000279968268021/10000000000000000 : ℝ)^4163 := by
      have hnat : (10001138240150410511 : ℕ)^1024*10000000000000000^4163 ≤ 10000279968268021^4163*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001138240150410511 10000000000000000000 10000279968268021 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000279968268021/10000000000000000 : ℝ)) (X := (10001138240150410511/10000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100072007882553749507/100000000000000000000 : ℝ) ≤ (625110671484541/625000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (100072007882553749507/100000000000000000000 : ℝ)^1024 ≤ (625110671484541/625000000000000 : ℝ)^4163 := by
      have hnat : (100072007882553749507 : ℕ)^1024*625000000000000^4163 ≤ 625110671484541^4163*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100072007882553749507 100000000000000000000 625110671484541 625000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625110671484541/625000000000000 : ℝ)) (X := (100072007882553749507/100000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6258289585225212119/6250000000000000000 : ℝ) ≤ (10003261519237291/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (6258289585225212119/6250000000000000000 : ℝ)^1024 ≤ (10003261519237291/10000000000000000 : ℝ)^4163 := by
      have hnat : (6258289585225212119 : ℕ)^1024*10000000000000000^4163 ≤ 10003261519237291^4163*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6258289585225212119 6250000000000000000 10003261519237291 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003261519237291/10000000000000000 : ℝ)) (X := (6258289585225212119/6250000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1138240150410511/20000000000000000000 : ℝ) ≤ ((74905162470775896173/74930000000000000000 : ℝ)+2*(298155096927/149860000000000 : ℝ)*(4517/50000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (74905162470775896173/74930000000000000000 : ℝ)+2*(298155096927/149860000000000 : ℝ)*(4517/50000 : ℝ)=(10000279968268021/10000000000000000 : ℝ) by norm_num, show 1+2*(1138240150410511/20000000000000000000 : ℝ)=(10001138240150410511/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8289585225212119/12500000000000000000 : ℝ)+(1138240150410511/20000000000000000000 : ℝ) ≤ ((74905162470775896173/74930000000000000000 : ℝ)+(298155096927/149860000000000 : ℝ)*((16527/100000 : ℝ)+(4517/50000 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (74905162470775896173/74930000000000000000 : ℝ)+(298155096927/149860000000000 : ℝ)*((16527/100000 : ℝ)+(4517/50000 : ℝ))=(625110671484541/625000000000000 : ℝ) by norm_num, show 1+(8289585225212119/12500000000000000000 : ℝ)+(1138240150410511/20000000000000000000 : ℝ)=(100072007882553749507/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8289585225212119/12500000000000000000 : ℝ) ≤ ((74905162470775896173/74930000000000000000 : ℝ)+2*(298155096927/149860000000000 : ℝ)*(16527/100000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (74905162470775896173/74930000000000000000 : ℝ)+2*(298155096927/149860000000000 : ℝ)*(16527/100000 : ℝ)=(10003261519237291/10000000000000000 : ℝ) by norm_num, show 1+2*(8289585225212119/12500000000000000000 : ℝ)=(6258289585225212119/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (74905162470775896173/74930000000000000000 : ℝ)*(X 1 0+X 2 0)+(298155096927/149860000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (4517/50000 : ℝ)) (hi := (16527/100000 : ℝ)) (c := (74905162470775896173/74930000000000000000 : ℝ)) (alpha := (298155096927/149860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (74905162470775896173/74930000000000000000 : ℝ)*(X 0 1+X 2 1)+(298155096927/149860000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (4517/50000 : ℝ)) (hi := (16527/100000 : ℝ)) (c := (74905162470775896173/74930000000000000000 : ℝ)) (alpha := (298155096927/149860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (74905162470775896173/74930000000000000000 : ℝ)*(X 0 2+X 1 2)+(298155096927/149860000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (4517/50000 : ℝ)) (hi := (16527/100000 : ℝ)) (c := (74905162470775896173/74930000000000000000 : ℝ)) (alpha := (298155096927/149860000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-541705881/2500000000 : ℝ)*X 0 0+(543001629/1000000000 : ℝ)*X 0 1+(5231320399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669248747/1250000000 : ℝ)*X 1 0+(-283551023/1250000000 : ℝ)*X 1 1+(2615660133/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353990063/10000000000 : ℝ)*X 2 0+(2615660179/5000000000 : ℝ)*X 2 1+(-1134203973/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2181745729/5000000000 : ℝ)*X 0 0+(1042648529/2500000000 : ℝ)*X 0 1+(285329619/625000000 : ℝ)*X 0 2+(2181745729/5000000000 : ℝ)*X 1 0+(1042648529/2500000000 : ℝ)*X 1 1+(285329619/625000000 : ℝ)*X 1 2+(2181745729/5000000000 : ℝ)*X 2 0+(1042648529/2500000000 : ℝ)*X 2 1+(285329619/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1083420999/5000000000 : ℝ)*X 0 0+(523209553/1000000000 : ℝ)*X 0 1+(3393273/6250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530368057/1000000000 : ℝ)*X 1 0+(-1035246081/5000000000 : ℝ)*X 1 1+(1085847303/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060736247/2000000000 : ℝ)*X 2 0+(2714618023/5000000000 : ℝ)*X 2 1+(-20704919/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((872705579/2000000000 : ℝ)*X 0 0+(2281867141/5000000000 : ℝ)*X 0 1+(2086071331/5000000000 : ℝ)*X 0 2+(872705579/2000000000 : ℝ)*X 1 0+(2281867141/5000000000 : ℝ)*X 1 1+(2086071331/5000000000 : ℝ)*X 1 2+(872705579/2000000000 : ℝ)*X 2 0+(2281867141/5000000000 : ℝ)*X 2 1+(2086071331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4623434649468594764065777617/936625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1381706481/100000000000000 : ℝ)*(base19) + (1307746641/100000000000000 : ℝ)*(base23) + (83383937/100000000000000 : ℝ)*(lower2) + (23176309/50000000000000 : ℝ)*(upper3) + (191993977/100000000000000 : ℝ)*(upper5) + (1891646644192257/50000000000000 : ℝ)*(major0) + (1891646644192257/50000000000000 : ℝ)*(major1) + (1891646644192257/50000000000000 : ℝ)*(major2) + (5032837284839941/100000000000000 : ℝ)*(sp0) + (25164317352109/500000000000 : ℝ)*(sp1) + (5032863544381641/100000000000000 : ℝ)*(sp2) + (2533711052495787/100000000000000 : ℝ)*(sp3) + (27567288341/100000000000000 : ℝ)*(sp4) + (10507602593/100000000000000 : ℝ)*(sp7) + (126686078004919/5000000000000 : ℝ)*(f.failure) + (2516432426064141/50000000000000 : ℝ)*(f.sum) + (20730982858431/7493000000000000000000000000 : ℝ)*base65 + (15475772364485032461/3746500000000000000000000000000000 : ℝ)*base67 + (12473203124207532461/3746500000000000000000000000000000 : ℝ)*base69 + (20957056059185532461/3746500000000000000000000000000000 : ℝ)*base71 + (1607596818919/468312500000000000000000000 : ℝ)*base73 + (50175006122851032461/3746500000000000000000000000000000 : ℝ)*base75 + (404574979023967539/3746500000000000000000000000000000 : ℝ)*base78 + (7065281271988032461/3746500000000000000000000000000000 : ℝ)*base79 + (22878637148937/3746500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (259501/250000000000000000000 : ℝ)*base90 + (259501/250000000000000000000 : ℝ)*base92 + (259501/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3627381736912478797386464361/1873250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370243873/100000000000000 : ℝ)*(base19) + (1070407/97656250000 : ℝ)*(base23) + (2000469/50000000000000 : ℝ)*(upper2) + (19757733/50000000000000 : ℝ)*(upper5) + (1906549346717519/50000000000000 : ℝ)*(major0) + (1906549346717519/50000000000000 : ℝ)*(major1) + (1906549346717519/50000000000000 : ℝ)*(major2) + (2056942193/100000000000000 : ℝ)*(sp0) + (3303079397/100000000000000 : ℝ)*(sp1) + (598937569/5000000000000 : ℝ)*(sp2) + (5072512631258457/100000000000000 : ℝ)*(sp4) + (5072511014877381/100000000000000 : ℝ)*(sp5) + (5072501613352503/100000000000000 : ℝ)*(sp6) + (2553682634122389/100000000000000 : ℝ)*(sp7) + (2553682634122389/100000000000000 : ℝ)*(f.failure) + (5072514688200651/100000000000000 : ℝ)*(f.sum) + (7980765717543/1498600000000000000000000000 : ℝ)*base66 + (9222615455733654787/3746500000000000000000000000000000 : ℝ)*base67 + (16246511518848154787/3746500000000000000000000000000000 : ℝ)*base69 + (9902112818799845213/3746500000000000000000000000000000 : ℝ)*base72 + (15152225018361/3746500000000000000000000000 : ℝ)*base73 + (6403382118916845213/3746500000000000000000000000000000 : ℝ)*base76 + (22102989082289345213/3746500000000000000000000000000000 : ℝ)*base78 + (47288826250773345213/3746500000000000000000000000000000 : ℝ)*base80 + (1104905296449/936625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (32443369/5000000000000000000000 : ℝ)*base89 + (32443369/5000000000000000000000 : ℝ)*base91 + (32443369/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1134_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2963/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1134_s4_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542473591/2500000000 : ℝ)*x 0 + (5402276853/10000000000 : ℝ)*x 1 + (5257051023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542473591/2500000000 : ℝ)^8327 ≤ (3295695209099/25000000000000 : ℝ)^6279 := by
    have hnat : (542473591 : ℕ)^8327*25000000000000^6279 ≤ 3295695209099^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542473591 2500000000 3295695209099 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5402276853/10000000000 : ℝ)^8327 ≤ (4419288321051/10000000000000 : ℝ)^6279 := by
    have hnat : (5402276853 : ℕ)^8327*10000000000000^6279 ≤ 4419288321051^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5402276853 10000000000 4419288321051 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257051023/10000000000 : ℝ)^8327 ≤ (5328041992827/12500000000000 : ℝ)^6279 := by
    have hnat : (5257051023 : ℕ)^8327*12500000000000^6279 ≤ 5328041992827^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257051023 10000000000 5328041992827 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542473591/2500000000 : ℝ), (5402276853/10000000000 : ℝ), (5257051023/10000000000 : ℝ)] ![(3295695209099/25000000000000 : ℝ), (4419288321051/10000000000000 : ℝ), (5328041992827/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542473591/2500000000 : ℝ)|^8327 ≤ (3295695209099/25000000000000 : ℝ)^6279
        have hw : |(-542473591/2500000000 : ℝ)|=(542473591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5402276853/10000000000 : ℝ)|^8327 ≤ (4419288321051/10000000000000 : ℝ)^6279
        have hw : |(5402276853/10000000000 : ℝ)|=(5402276853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257051023/10000000000 : ℝ)|^8327 ≤ (5328041992827/12500000000000 : ℝ)^6279
        have hw : |(5257051023/10000000000 : ℝ)|=(5257051023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s4_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347066981/10000000000 : ℝ)*x 0 + (-3505787/15625000 : ℝ)*x 1 + (5257051287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347066981/10000000000 : ℝ)^8327 ≤ (43594934104419/100000000000000 : ℝ)^6279 := by
    have hnat : (5347066981 : ℕ)^8327*100000000000000^6279 ≤ 43594934104419^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347066981 10000000000 43594934104419 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3505787/15625000 : ℝ)^8327 ≤ (2756145420861/20000000000000 : ℝ)^6279 := by
    have hnat : (3505787 : ℕ)^8327*20000000000000^6279 ≤ 2756145420861^6279*15625000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3505787 15625000 2756145420861 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5257051287/10000000000 : ℝ)^8327 ≤ (21312169390651/50000000000000 : ℝ)^6279 := by
    have hnat : (5257051287 : ℕ)^8327*50000000000000^6279 ≤ 21312169390651^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257051287 10000000000 21312169390651 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347066981/10000000000 : ℝ), (-3505787/15625000 : ℝ), (5257051287/10000000000 : ℝ)] ![(43594934104419/100000000000000 : ℝ), (2756145420861/20000000000000 : ℝ), (21312169390651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347066981/10000000000 : ℝ)|^8327 ≤ (43594934104419/100000000000000 : ℝ)^6279
        have hw : |(5347066981/10000000000 : ℝ)|=(5347066981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3505787/15625000 : ℝ)|^8327 ≤ (2756145420861/20000000000000 : ℝ)^6279
        have hw : |(-3505787/15625000 : ℝ)|=(3505787/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5257051287/10000000000 : ℝ)|^8327 ≤ (21312169390651/50000000000000 : ℝ)^6279
        have hw : |(5257051287/10000000000 : ℝ)|=(5257051287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s4_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5347067597/10000000000 : ℝ)*x 0 + (5257050407/10000000000 : ℝ)*x 1 + (-2243704023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347067597/10000000000 : ℝ)^8327 ≤ (21797470382401/50000000000000 : ℝ)^6279 := by
    have hnat : (5347067597 : ℕ)^8327*50000000000000^6279 ≤ 21797470382401^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347067597 10000000000 21797470382401 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5257050407/10000000000 : ℝ)^8327 ≤ (21312164659507/50000000000000 : ℝ)^6279 := by
    have hnat : (5257050407 : ℕ)^8327*50000000000000^6279 ≤ 21312164659507^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5257050407 10000000000 21312164659507 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243704023/10000000000 : ℝ)^8327 ≤ (13780729898127/100000000000000 : ℝ)^6279 := by
    have hnat : (2243704023 : ℕ)^8327*100000000000000^6279 ≤ 13780729898127^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243704023 10000000000 13780729898127 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347067597/10000000000 : ℝ), (5257050407/10000000000 : ℝ), (-2243704023/10000000000 : ℝ)] ![(21797470382401/50000000000000 : ℝ), (21312164659507/50000000000000 : ℝ), (13780729898127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347067597/10000000000 : ℝ)|^8327 ≤ (21797470382401/50000000000000 : ℝ)^6279
        have hw : |(5347067597/10000000000 : ℝ)|=(5347067597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5257050407/10000000000 : ℝ)|^8327 ≤ (21312164659507/50000000000000 : ℝ)^6279
        have hw : |(5257050407/10000000000 : ℝ)|=(5257050407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2243704023/10000000000 : ℝ)|^8327 ≤ (13780729898127/100000000000000 : ℝ)^6279
        have hw : |(-2243704023/10000000000 : ℝ)|=(2243704023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s4_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365322157/10000000000 : ℝ)*x 0 + (2111730197/5000000000 : ℝ)*x 1 + (4511932243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365322157/10000000000 : ℝ)^8327 ≤ (33312071876223/100000000000000 : ℝ)^6279 := by
    have hnat : (4365322157 : ℕ)^8327*100000000000000^6279 ≤ 33312071876223^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365322157 10000000000 33312071876223 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2111730197/5000000000 : ℝ)^8327 ≤ (6376817230443/20000000000000 : ℝ)^6279 := by
    have hnat : (2111730197 : ℕ)^8327*20000000000000^6279 ≤ 6376817230443^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2111730197 5000000000 6376817230443 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4511932243/10000000000 : ℝ)^8327 ≤ (696076839197/2000000000000 : ℝ)^6279 := by
    have hnat : (4511932243 : ℕ)^8327*2000000000000^6279 ≤ 696076839197^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511932243 10000000000 696076839197 2000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365322157/10000000000 : ℝ), (2111730197/5000000000 : ℝ), (4511932243/10000000000 : ℝ)] ![(33312071876223/100000000000000 : ℝ), (6376817230443/20000000000000 : ℝ), (696076839197/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365322157/10000000000 : ℝ)|^8327 ≤ (33312071876223/100000000000000 : ℝ)^6279
        have hw : |(4365322157/10000000000 : ℝ)|=(4365322157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2111730197/5000000000 : ℝ)|^8327 ≤ (6376817230443/20000000000000 : ℝ)^6279
        have hw : |(2111730197/5000000000 : ℝ)|=(2111730197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4511932243/10000000000 : ℝ)|^8327 ≤ (696076839197/2000000000000 : ℝ)^6279
        have hw : |(4511932243/10000000000 : ℝ)|=(4511932243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s4_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542475597/2500000000 : ℝ)*x 0 + (2628732599/5000000000 : ℝ)*x 1 + (5401860373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542475597/2500000000 : ℝ)^8327 ≤ (2636569096957/20000000000000 : ℝ)^6279 := by
    have hnat : (542475597 : ℕ)^8327*20000000000000^6279 ≤ 2636569096957^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542475597 2500000000 2636569096957 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628732599/5000000000 : ℝ)^8327 ≤ (42628789458199/100000000000000 : ℝ)^6279 := by
    have hnat : (2628732599 : ℕ)^8327*100000000000000^6279 ≤ 42628789458199^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628732599 5000000000 42628789458199 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5401860373/10000000000 : ℝ)^8327 ≤ (44188365043589/100000000000000 : ℝ)^6279 := by
    have hnat : (5401860373 : ℕ)^8327*100000000000000^6279 ≤ 44188365043589^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401860373 10000000000 44188365043589 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542475597/2500000000 : ℝ), (2628732599/5000000000 : ℝ), (5401860373/10000000000 : ℝ)] ![(2636569096957/20000000000000 : ℝ), (42628789458199/100000000000000 : ℝ), (44188365043589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542475597/2500000000 : ℝ)|^8327 ≤ (2636569096957/20000000000000 : ℝ)^6279
        have hw : |(-542475597/2500000000 : ℝ)|=(542475597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628732599/5000000000 : ℝ)|^8327 ≤ (42628789458199/100000000000000 : ℝ)^6279
        have hw : |(2628732599/5000000000 : ℝ)|=(2628732599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5401860373/10000000000 : ℝ)|^8327 ≤ (44188365043589/100000000000000 : ℝ)^6279
        have hw : |(5401860373/10000000000 : ℝ)|=(5401860373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s4_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062059537/2000000000 : ℝ)*x 0 + (-83955753/400000000 : ℝ)*x 1 + (2700930257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062059537/2000000000 : ℝ)^8327 ≤ (5399727452231/12500000000000 : ℝ)^6279 := by
    have hnat : (1062059537 : ℕ)^8327*12500000000000^6279 ≤ 5399727452231^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062059537 2000000000 5399727452231 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83955753/400000000 : ℝ)^8327 ≤ (6306906894027/50000000000000 : ℝ)^6279 := by
    have hnat : (83955753 : ℕ)^8327*50000000000000^6279 ≤ 6306906894027^6279*400000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83955753 400000000 6306906894027 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700930257/5000000000 : ℝ)^8327 ≤ (44188366573203/100000000000000 : ℝ)^6279 := by
    have hnat : (2700930257 : ℕ)^8327*100000000000000^6279 ≤ 44188366573203^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700930257 5000000000 44188366573203 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062059537/2000000000 : ℝ), (-83955753/400000000 : ℝ), (2700930257/5000000000 : ℝ)] ![(5399727452231/12500000000000 : ℝ), (6306906894027/50000000000000 : ℝ), (44188366573203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062059537/2000000000 : ℝ)|^8327 ≤ (5399727452231/12500000000000 : ℝ)^6279
        have hw : |(1062059537/2000000000 : ℝ)|=(1062059537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83955753/400000000 : ℝ)|^8327 ≤ (6306906894027/50000000000000 : ℝ)^6279
        have hw : |(-83955753/400000000 : ℝ)|=(83955753/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700930257/5000000000 : ℝ)|^8327 ≤ (44188366573203/100000000000000 : ℝ)^6279
        have hw : |(2700930257/5000000000 : ℝ)|=(2700930257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s4_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310297893/10000000000 : ℝ)*x 0 + (5401860301/10000000000 : ℝ)*x 1 + (-2098893833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310297893/10000000000 : ℝ)^8327 ≤ (43197821861753/100000000000000 : ℝ)^6279 := by
    have hnat : (5310297893 : ℕ)^8327*100000000000000^6279 ≤ 43197821861753^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310297893 10000000000 43197821861753 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5401860301/10000000000 : ℝ)^8327 ≤ (4418836426251/10000000000000 : ℝ)^6279 := by
    have hnat : (5401860301 : ℕ)^8327*10000000000000^6279 ≤ 4418836426251^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401860301 10000000000 4418836426251 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098893833/10000000000 : ℝ)^8327 ≤ (12613813851813/100000000000000 : ℝ)^6279 := by
    have hnat : (2098893833 : ℕ)^8327*100000000000000^6279 ≤ 12613813851813^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098893833 10000000000 12613813851813 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310297893/10000000000 : ℝ), (5401860301/10000000000 : ℝ), (-2098893833/10000000000 : ℝ)] ![(43197821861753/100000000000000 : ℝ), (4418836426251/10000000000000 : ℝ), (12613813851813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310297893/10000000000 : ℝ)|^8327 ≤ (43197821861753/100000000000000 : ℝ)^6279
        have hw : |(5310297893/10000000000 : ℝ)|=(5310297893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5401860301/10000000000 : ℝ)|^8327 ≤ (4418836426251/10000000000000 : ℝ)^6279
        have hw : |(5401860301/10000000000 : ℝ)|=(5401860301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2098893833/10000000000 : ℝ)|^8327 ≤ (12613813851813/100000000000000 : ℝ)^6279
        have hw : |(-2098893833/10000000000 : ℝ)|=(2098893833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s4_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (272833523/625000000 : ℝ)*x 0 + (1127776889/2500000000 : ℝ)*x 1 + (1056072157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272833523/625000000 : ℝ)^8327 ≤ (6662443138517/20000000000000 : ℝ)^6279 := by
    have hnat : (272833523 : ℕ)^8327*20000000000000^6279 ≤ 6662443138517^6279*625000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272833523 625000000 6662443138517 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127776889/2500000000 : ℝ)^8327 ≤ (17397702957279/50000000000000 : ℝ)^6279 := by
    have hnat : (1127776889 : ℕ)^8327*50000000000000^6279 ≤ 17397702957279^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127776889 2500000000 17397702957279 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056072157/2500000000 : ℝ)^8327 ≤ (15946189183789/50000000000000 : ℝ)^6279 := by
    have hnat : (1056072157 : ℕ)^8327*50000000000000^6279 ≤ 15946189183789^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056072157 2500000000 15946189183789 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272833523/625000000 : ℝ), (1127776889/2500000000 : ℝ), (1056072157/2500000000 : ℝ)] ![(6662443138517/20000000000000 : ℝ), (17397702957279/50000000000000 : ℝ), (15946189183789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272833523/625000000 : ℝ)|^8327 ≤ (6662443138517/20000000000000 : ℝ)^6279
        have hw : |(272833523/625000000 : ℝ)|=(272833523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1127776889/2500000000 : ℝ)|^8327 ≤ (17397702957279/50000000000000 : ℝ)^6279
        have hw : |(1127776889/2500000000 : ℝ)|=(1127776889/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056072157/2500000000 : ℝ)|^8327 ≤ (15946189183789/50000000000000 : ℝ)^6279
        have hw : |(1056072157/2500000000 : ℝ)|=(1056072157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2963/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (279/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2963/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10611/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2963/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10611/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2963/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10611/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2963/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10611/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2963/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10611/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2963/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10611/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10611/100000 : ℝ) ^ (4163/1024 : ℝ) ≤ (10946639054462873/100000000000000000000 : ℝ) := by
    have hpowers : (10611/100000 : ℝ)^4163 ≤ (10946639054462873/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10611 : ℕ)^4163*100000000000000000000^1024 ≤ 10946639054462873^1024*100000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10611 100000 10946639054462873 100000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10611/100000 : ℝ)) (X := (10946639054462873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2963/20000 : ℝ) ^ (4163/1024 : ℝ) ≤ (10628840757005427/25000000000000000000 : ℝ) := by
    have hpowers : (2963/20000 : ℝ)^4163 ≤ (10628840757005427/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2963 : ℕ)^4163*25000000000000000000^1024 ≤ 10628840757005427^1024*20000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2963 20000 10628840757005427 25000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2963/20000 : ℝ)) (X := (10628840757005427/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010946639054462873/50000000000000000000 : ℝ) ≤ (10000538478659001/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50010946639054462873/50000000000000000000 : ℝ)^1024 ≤ (10000538478659001/10000000000000000 : ℝ)^4163 := by
      have hnat : (50010946639054462873 : ℕ)^1024*10000000000000000^4163 ≤ 10000538478659001^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010946639054462873 50000000000000000000 10000538478659001 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538478659001/10000000000000000 : ℝ)) (X := (50010946639054462873/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100053462002082484581/100000000000000000000 : ℝ) ≤ (5000657387211953/5000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (100053462002082484581/100000000000000000000 : ℝ)^1024 ≤ (5000657387211953/5000000000000000 : ℝ)^4163 := by
      have hnat : (100053462002082484581 : ℕ)^1024*5000000000000000^4163 ≤ 5000657387211953^4163*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100053462002082484581 100000000000000000000 5000657387211953 5000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000657387211953/5000000000000000 : ℝ)) (X := (100053462002082484581/100000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12510628840757005427/12500000000000000000 : ℝ) ≤ (10002091070188811/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (12510628840757005427/12500000000000000000 : ℝ)^1024 ≤ (10002091070188811/10000000000000000 : ℝ)^4163 := by
      have hnat : (12510628840757005427 : ℕ)^1024*10000000000000000^4163 ≤ 10002091070188811^4163*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510628840757005427 12500000000000000000 10002091070188811 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002091070188811/10000000000000000 : ℝ)) (X := (12510628840757005427/12500000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10946639054462873/100000000000000000000 : ℝ) ≤ ((21012894607779813147/21020000000000000000 : ℝ)+2*(155259152981/84080000000000 : ℝ)*(10611/100000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (21012894607779813147/21020000000000000000 : ℝ)+2*(155259152981/84080000000000 : ℝ)*(10611/100000 : ℝ)=(10000538478659001/10000000000000000 : ℝ) by norm_num, show 1+2*(10946639054462873/100000000000000000000 : ℝ)=(50010946639054462873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10628840757005427/25000000000000000000 : ℝ)+(10946639054462873/100000000000000000000 : ℝ) ≤ ((21012894607779813147/21020000000000000000 : ℝ)+(155259152981/84080000000000 : ℝ)*((2963/20000 : ℝ)+(10611/100000 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (21012894607779813147/21020000000000000000 : ℝ)+(155259152981/84080000000000 : ℝ)*((2963/20000 : ℝ)+(10611/100000 : ℝ))=(5000657387211953/5000000000000000 : ℝ) by norm_num, show 1+(10628840757005427/25000000000000000000 : ℝ)+(10946639054462873/100000000000000000000 : ℝ)=(100053462002082484581/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10628840757005427/25000000000000000000 : ℝ) ≤ ((21012894607779813147/21020000000000000000 : ℝ)+2*(155259152981/84080000000000 : ℝ)*(2963/20000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (21012894607779813147/21020000000000000000 : ℝ)+2*(155259152981/84080000000000 : ℝ)*(2963/20000 : ℝ)=(10002091070188811/10000000000000000 : ℝ) by norm_num, show 1+2*(10628840757005427/25000000000000000000 : ℝ)=(12510628840757005427/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21012894607779813147/21020000000000000000 : ℝ)*(X 1 0+X 2 0)+(155259152981/84080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (2963/20000 : ℝ)) (c := (21012894607779813147/21020000000000000000 : ℝ)) (alpha := (155259152981/84080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21012894607779813147/21020000000000000000 : ℝ)*(X 0 1+X 2 1)+(155259152981/84080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (2963/20000 : ℝ)) (c := (21012894607779813147/21020000000000000000 : ℝ)) (alpha := (155259152981/84080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21012894607779813147/21020000000000000000 : ℝ)*(X 0 2+X 1 2)+(155259152981/84080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (10611/100000 : ℝ)) (hi := (2963/20000 : ℝ)) (c := (21012894607779813147/21020000000000000000 : ℝ)) (alpha := (155259152981/84080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-542473591/2500000000 : ℝ)*X 0 0+(5402276853/10000000000 : ℝ)*X 0 1+(5257051023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347066981/10000000000 : ℝ)*X 1 0+(-3505787/15625000 : ℝ)*X 1 1+(5257051287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347067597/10000000000 : ℝ)*X 2 0+(5257050407/10000000000 : ℝ)*X 2 1+(-2243704023/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365322157/10000000000 : ℝ)*X 0 0+(2111730197/5000000000 : ℝ)*X 0 1+(4511932243/10000000000 : ℝ)*X 0 2+(4365322157/10000000000 : ℝ)*X 1 0+(2111730197/5000000000 : ℝ)*X 1 1+(4511932243/10000000000 : ℝ)*X 1 2+(4365322157/10000000000 : ℝ)*X 2 0+(2111730197/5000000000 : ℝ)*X 2 1+(4511932243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-542475597/2500000000 : ℝ)*X 0 0+(2628732599/5000000000 : ℝ)*X 0 1+(5401860373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062059537/2000000000 : ℝ)*X 1 0+(-83955753/400000000 : ℝ)*X 1 1+(2700930257/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310297893/10000000000 : ℝ)*X 2 0+(5401860301/10000000000 : ℝ)*X 2 1+(-2098893833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((272833523/625000000 : ℝ)*X 0 0+(1127776889/2500000000 : ℝ)*X 0 1+(1056072157/2500000000 : ℝ)*X 0 2+(272833523/625000000 : ℝ)*X 1 0+(1127776889/2500000000 : ℝ)*X 1 1+(1056072157/2500000000 : ℝ)*X 1 2+(272833523/625000000 : ℝ)*X 2 0+(1127776889/2500000000 : ℝ)*X 2 1+(1056072157/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1527186133549003951051449351/131375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56716627/10000000000000 : ℝ)*(base23) + (79697027/25000000000000 : ℝ)*(lower2) + (45446423/25000000000000 : ℝ)*(upper3) + (61764561/25000000000000 : ℝ)*(lower4) + (121939361/100000000000000 : ℝ)*(upper5) + (647024215843163/12500000000000 : ℝ)*(major0) + (647024215843163/12500000000000 : ℝ)*(major1) + (647024215843163/12500000000000 : ℝ)*(major2) + (6885821657244709/100000000000000 : ℝ)*(sp0) + (6885821657244709/100000000000000 : ℝ)*(sp1) + (6885807717897771/100000000000000 : ℝ)*(sp2) + (1733275769840951/50000000000000 : ℝ)*(sp3) + (3343045167/25000000000000 : ℝ)*(sp6) + (1386907623/10000000000000 : ℝ)*(sp7) + (866641352189533/25000000000000 : ℝ)*(f.failure) + (6885821657244709/100000000000000 : ℝ)*(f.sum) + (110946554799/8210937500000000000000000 : ℝ)*base66 + (2848273522099463961/262750000000000000000000000000000 : ℝ)*base67 + (7588186027463961/262750000000000000000000000000000 : ℝ)*base69 + (1899776307189963961/262750000000000000000000000000000 : ℝ)*base71 + (2379928385871/525500000000000000000000000 : ℝ)*base74 + (661151701533463961/262750000000000000000000000000000 : ℝ)*base75 + (4149571794344463961/262750000000000000000000000000000 : ℝ)*base77 + (1455335115727463961/262750000000000000000000000000000 : ℝ)*base79 + (10040365909093/1051000000000000000000000000 : ℝ)*base82 + (2320593/1250000000000000000000 : ℝ)*base89 + (2320593/1250000000000000000000 : ℝ)*base91 + (2320593/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26604315439151263607009799/26275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (575579919/100000000000000 : ℝ)*(base19) + (103292567/10000000000000 : ℝ)*(base23) + (27612969/25000000000000 : ℝ)*(upper2) + (52034309/100000000000000 : ℝ)*(upper3) + (320314957/100000000000000 : ℝ)*(upper5) + (260299147527639/5000000000000 : ℝ)*(major0) + (260299147527639/5000000000000 : ℝ)*(major1) + (260299147527639/5000000000000 : ℝ)*(major2) + (857056473/4000000000000 : ℝ)*(sp1) + (3652267453/20000000000000 : ℝ)*(sp2) + (6925450221364811/100000000000000 : ℝ)*(sp4) + (6925428219373067/100000000000000 : ℝ)*(sp5) + (6925430927101877/100000000000000 : ℝ)*(sp6) + (871628911497407/25000000000000 : ℝ)*(sp7) + (871628911497407/25000000000000 : ℝ)*(f.failure) + (6925450221364811/100000000000000 : ℝ)*(f.sum) + (3380995970941/1051000000000000000000000000 : ℝ)*base66 + (1821538082101780067/105100000000000000000000000000000 : ℝ)*base68 + (38405252279119933/105100000000000000000000000000000 : ℝ)*base69 + (589851694249580067/105100000000000000000000000000000 : ℝ)*base72 + (537141385031/131375000000000000000000000 : ℝ)*base74 + (1049706683341880067/105100000000000000000000000000000 : ℝ)*base76 + (694178909294180067/105100000000000000000000000000000 : ℝ)*base78 + (1378757484197180067/105100000000000000000000000000000 : ℝ)*base80 + (952396515147/1051000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1177147/1250000000000000000000 : ℝ)*base89 + (1177147/1250000000000000000000 : ℝ)*base91 + (1177147/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1134_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2963/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10611/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1134_s5_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-542637623/2500000000 : ℝ)*x 0 + (5395121343/10000000000 : ℝ)*x 1 + (2631887897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542637623/2500000000 : ℝ)^8327 ≤ (13188067437077/100000000000000 : ℝ)^6279 := by
    have hnat : (542637623 : ℕ)^8327*100000000000000^6279 ≤ 13188067437077^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542637623 2500000000 13188067437077 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395121343/10000000000 : ℝ)^8327 ≤ (22057636369287/50000000000000 : ℝ)^6279 := by
    have hnat : (5395121343 : ℕ)^8327*50000000000000^6279 ≤ 22057636369287^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395121343 10000000000 22057636369287 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631887897/5000000000 : ℝ)^8327 ≤ (42696659799819/100000000000000 : ℝ)^6279 := by
    have hnat : (2631887897 : ℕ)^8327*100000000000000^6279 ≤ 42696659799819^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631887897 5000000000 42696659799819 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-542637623/2500000000 : ℝ), (5395121343/10000000000 : ℝ), (2631887897/5000000000 : ℝ)] ![(13188067437077/100000000000000 : ℝ), (22057636369287/50000000000000 : ℝ), (42696659799819/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-542637623/2500000000 : ℝ)|^8327 ≤ (13188067437077/100000000000000 : ℝ)^6279
        have hw : |(-542637623/2500000000 : ℝ)|=(542637623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395121343/10000000000 : ℝ)|^8327 ≤ (22057636369287/50000000000000 : ℝ)^6279
        have hw : |(5395121343/10000000000 : ℝ)|=(5395121343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631887897/5000000000 : ℝ)|^8327 ≤ (42696659799819/100000000000000 : ℝ)^6279
        have hw : |(2631887897/5000000000 : ℝ)|=(2631887897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s5_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345273967/10000000000 : ℝ)*x 0 + (-2237201651/10000000000 : ℝ)*x 1 + (5263775811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345273967/10000000000 : ℝ)^8327 ≤ (174302194167/400000000000 : ℝ)^6279 := by
    have hnat : (5345273967 : ℕ)^8327*400000000000^6279 ≤ 174302194167^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345273967 10000000000 174302194167 400000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2237201651/10000000000 : ℝ)^8327 ≤ (3431947865513/25000000000000 : ℝ)^6279 := by
    have hnat : (2237201651 : ℕ)^8327*25000000000000^6279 ≤ 3431947865513^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237201651 10000000000 3431947865513 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263775811/10000000000 : ℝ)^8327 ≤ (42696659982689/100000000000000 : ℝ)^6279 := by
    have hnat : (5263775811 : ℕ)^8327*100000000000000^6279 ≤ 42696659982689^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263775811 10000000000 42696659982689 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345273967/10000000000 : ℝ), (-2237201651/10000000000 : ℝ), (5263775811/10000000000 : ℝ)] ![(174302194167/400000000000 : ℝ), (3431947865513/25000000000000 : ℝ), (42696659982689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345273967/10000000000 : ℝ)|^8327 ≤ (174302194167/400000000000 : ℝ)^6279
        have hw : |(5345273967/10000000000 : ℝ)|=(5345273967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2237201651/10000000000 : ℝ)|^8327 ≤ (3431947865513/25000000000000 : ℝ)^6279
        have hw : |(-2237201651/10000000000 : ℝ)|=(2237201651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263775811/10000000000 : ℝ)|^8327 ≤ (42696659982689/100000000000000 : ℝ)^6279
        have hw : |(5263775811/10000000000 : ℝ)|=(5263775811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s5_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672637137/5000000000 : ℝ)*x 0 + (1315943887/2500000000 : ℝ)*x 1 + (-223720159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672637137/5000000000 : ℝ)^8327 ≤ (21787775930383/50000000000000 : ℝ)^6279 := by
    have hnat : (2672637137 : ℕ)^8327*50000000000000^6279 ≤ 21787775930383^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672637137 5000000000 21787775930383 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315943887/2500000000 : ℝ)^8327 ≤ (5337082144197/12500000000000 : ℝ)^6279 := by
    have hnat : (1315943887 : ℕ)^8327*12500000000000^6279 ≤ 5337082144197^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315943887 2500000000 5337082144197 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (223720159/1000000000 : ℝ)^8327 ≤ (13727790965661/100000000000000 : ℝ)^6279 := by
    have hnat : (223720159 : ℕ)^8327*100000000000000^6279 ≤ 13727790965661^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223720159 1000000000 13727790965661 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672637137/5000000000 : ℝ), (1315943887/2500000000 : ℝ), (-223720159/1000000000 : ℝ)] ![(21787775930383/50000000000000 : ℝ), (5337082144197/12500000000000 : ℝ), (13727790965661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672637137/5000000000 : ℝ)|^8327 ≤ (21787775930383/50000000000000 : ℝ)^6279
        have hw : |(2672637137/5000000000 : ℝ)|=(2672637137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315943887/2500000000 : ℝ)|^8327 ≤ (5337082144197/12500000000000 : ℝ)^6279
        have hw : |(1315943887/2500000000 : ℝ)|=(1315943887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-223720159/1000000000 : ℝ)|^8327 ≤ (13727790965661/100000000000000 : ℝ)^6279
        have hw : |(-223720159/1000000000 : ℝ)|=(223720159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s5_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545713007/1250000000 : ℝ)*x 0 + (4237197343/10000000000 : ℝ)*x 1 + (4498096297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545713007/1250000000 : ℝ)^8327 ≤ (33315936775177/100000000000000 : ℝ)^6279 := by
    have hnat : (545713007 : ℕ)^8327*100000000000000^6279 ≤ 33315936775177^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545713007 1250000000 33315936775177 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4237197343/10000000000 : ℝ)^8327 ≤ (6404337586387/20000000000000 : ℝ)^6279 := by
    have hnat : (4237197343 : ℕ)^8327*20000000000000^6279 ≤ 6404337586387^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237197343 10000000000 6404337586387 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4498096297/10000000000 : ℝ)^8327 ≤ (4332796909859/12500000000000 : ℝ)^6279 := by
    have hnat : (4498096297 : ℕ)^8327*12500000000000^6279 ≤ 4332796909859^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498096297 10000000000 4332796909859 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545713007/1250000000 : ℝ), (4237197343/10000000000 : ℝ), (4498096297/10000000000 : ℝ)] ![(33315936775177/100000000000000 : ℝ), (6404337586387/20000000000000 : ℝ), (4332796909859/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545713007/1250000000 : ℝ)|^8327 ≤ (33315936775177/100000000000000 : ℝ)^6279
        have hw : |(545713007/1250000000 : ℝ)|=(545713007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4237197343/10000000000 : ℝ)|^8327 ≤ (6404337586387/20000000000000 : ℝ)^6279
        have hw : |(4237197343/10000000000 : ℝ)|=(4237197343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4498096297/10000000000 : ℝ)|^8327 ≤ (4332796909859/12500000000000 : ℝ)^6279
        have hw : |(4498096297/10000000000 : ℝ)|=(4498096297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s5_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-108527801/500000000 : ℝ)*x 0 + (5264115287/10000000000 : ℝ)*x 1 + (2697390227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108527801/500000000 : ℝ)^8327 ≤ (6594055989941/50000000000000 : ℝ)^6279 := by
    have hnat : (108527801 : ℕ)^8327*50000000000000^6279 ≤ 6594055989941^6279*500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108527801 500000000 6594055989941 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264115287/10000000000 : ℝ)^8327 ≤ (21350155896643/50000000000000 : ℝ)^6279 := by
    have hnat : (5264115287 : ℕ)^8327*50000000000000^6279 ≤ 21350155896643^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264115287 10000000000 21350155896643 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697390227/5000000000 : ℝ)^8327 ≤ (11027894051909/25000000000000 : ℝ)^6279 := by
    have hnat : (2697390227 : ℕ)^8327*25000000000000^6279 ≤ 11027894051909^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697390227 5000000000 11027894051909 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108527801/500000000 : ℝ), (5264115287/10000000000 : ℝ), (2697390227/5000000000 : ℝ)] ![(6594055989941/50000000000000 : ℝ), (21350155896643/50000000000000 : ℝ), (11027894051909/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108527801/500000000 : ℝ)|^8327 ≤ (6594055989941/50000000000000 : ℝ)^6279
        have hw : |(-108527801/500000000 : ℝ)|=(108527801/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264115287/10000000000 : ℝ)|^8327 ≤ (21350155896643/50000000000000 : ℝ)^6279
        have hw : |(5264115287/10000000000 : ℝ)|=(5264115287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697390227/5000000000 : ℝ)|^8327 ≤ (11027894051909/25000000000000 : ℝ)^6279
        have hw : |(2697390227/5000000000 : ℝ)|=(2697390227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s5_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328004347/2500000000 : ℝ)*x 0 + (-2106196827/10000000000 : ℝ)*x 1 + (5394780443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328004347/2500000000 : ℝ)^8327 ≤ (43216372757943/100000000000000 : ℝ)^6279 := by
    have hnat : (1328004347 : ℕ)^8327*100000000000000^6279 ≤ 43216372757943^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328004347 2500000000 43216372757943 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106196827/10000000000 : ℝ)^8327 ≤ (2534410228043/20000000000000 : ℝ)^6279 := by
    have hnat : (2106196827 : ℕ)^8327*20000000000000^6279 ≤ 2534410228043^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106196827 10000000000 2534410228043 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394780443/10000000000 : ℝ)^8327 ≤ (8822315217671/20000000000000 : ℝ)^6279 := by
    have hnat : (5394780443 : ℕ)^8327*20000000000000^6279 ≤ 8822315217671^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394780443 10000000000 8822315217671 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328004347/2500000000 : ℝ), (-2106196827/10000000000 : ℝ), (5394780443/10000000000 : ℝ)] ![(43216372757943/100000000000000 : ℝ), (2534410228043/20000000000000 : ℝ), (8822315217671/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328004347/2500000000 : ℝ)|^8327 ≤ (43216372757943/100000000000000 : ℝ)^6279
        have hw : |(1328004347/2500000000 : ℝ)|=(1328004347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2106196827/10000000000 : ℝ)|^8327 ≤ (2534410228043/20000000000000 : ℝ)^6279
        have hw : |(-2106196827/10000000000 : ℝ)|=(2106196827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394780443/10000000000 : ℝ)|^8327 ≤ (8822315217671/20000000000000 : ℝ)^6279
        have hw : |(5394780443/10000000000 : ℝ)|=(5394780443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s5_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656008691/5000000000 : ℝ)*x 0 + (1078956089/2000000000 : ℝ)*x 1 + (-65818651/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656008691/5000000000 : ℝ)^8327 ≤ (5402046586651/12500000000000 : ℝ)^6279 := by
    have hnat : (2656008691 : ℕ)^8327*12500000000000^6279 ≤ 5402046586651^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656008691 5000000000 5402046586651 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078956089/2000000000 : ℝ)^8327 ≤ (22055788055021/50000000000000 : ℝ)^6279 := by
    have hnat : (1078956089 : ℕ)^8327*50000000000000^6279 ≤ 22055788055021^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078956089 2000000000 22055788055021 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65818651/312500000 : ℝ)^8327 ≤ (1267205118011/10000000000000 : ℝ)^6279 := by
    have hnat : (65818651 : ℕ)^8327*10000000000000^6279 ≤ 1267205118011^6279*312500000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65818651 312500000 1267205118011 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656008691/5000000000 : ℝ), (1078956089/2000000000 : ℝ), (-65818651/312500000 : ℝ)] ![(5402046586651/12500000000000 : ℝ), (22055788055021/50000000000000 : ℝ), (1267205118011/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656008691/5000000000 : ℝ)|^8327 ≤ (5402046586651/12500000000000 : ℝ)^6279
        have hw : |(2656008691/5000000000 : ℝ)|=(2656008691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078956089/2000000000 : ℝ)|^8327 ≤ (22055788055021/50000000000000 : ℝ)^6279
        have hw : |(1078956089/2000000000 : ℝ)|=(1078956089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-65818651/312500000 : ℝ)|^8327 ≤ (1267205118011/10000000000000 : ℝ)^6279
        have hw : |(-65818651/312500000 : ℝ)|=(65818651/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s5_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365714593/10000000000 : ℝ)*x 0 + (4497421683/10000000000 : ℝ)*x 1 + (4237874559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365714593/10000000000 : ℝ)^8327 ≤ (33316043413417/100000000000000 : ℝ)^6279 := by
    have hnat : (4365714593 : ℕ)^8327*100000000000000^6279 ≤ 33316043413417^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365714593 10000000000 33316043413417 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497421683/10000000000 : ℝ)^8327 ≤ (34655481261401/100000000000000 : ℝ)^6279 := by
    have hnat : (4497421683 : ℕ)^8327*100000000000000^6279 ≤ 34655481261401^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497421683 10000000000 34655481261401 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4237874559/10000000000 : ℝ)^8327 ≤ (6405695062313/20000000000000 : ℝ)^6279 := by
    have hnat : (4237874559 : ℕ)^8327*20000000000000^6279 ≤ 6405695062313^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4237874559 10000000000 6405695062313 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365714593/10000000000 : ℝ), (4497421683/10000000000 : ℝ), (4237874559/10000000000 : ℝ)] ![(33316043413417/100000000000000 : ℝ), (34655481261401/100000000000000 : ℝ), (6405695062313/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365714593/10000000000 : ℝ)|^8327 ≤ (33316043413417/100000000000000 : ℝ)^6279
        have hw : |(4365714593/10000000000 : ℝ)|=(4365714593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497421683/10000000000 : ℝ)|^8327 ≤ (34655481261401/100000000000000 : ℝ)^6279
        have hw : |(4497421683/10000000000 : ℝ)|=(4497421683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4237874559/10000000000 : ℝ)|^8327 ≤ (6405695062313/20000000000000 : ℝ)^6279
        have hw : |(4237874559/10000000000 : ℝ)|=(4237874559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (11303/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2817/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (279/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (279/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (279/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (279/2500 : ℝ) ^ (4163/1024 : ℝ) ≤ (2687668738903049/20000000000000000000 : ℝ) := by
    have hpowers : (279/2500 : ℝ)^4163 ≤ (2687668738903049/20000000000000000000 : ℝ)^1024 := by
      have hnat : (279 : ℕ)^4163*20000000000000000000^1024 ≤ 2687668738903049^1024*2500^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        279 2500 2687668738903049 20000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (279/2500 : ℝ)) (X := (2687668738903049/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (4163/1024 : ℝ) ≤ (36143843229305687/100000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^4163 ≤ (36143843229305687/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4163*100000000000000000000^1024 ≤ 36143843229305687^1024*20000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 36143843229305687 100000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (36143843229305687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002687668738903049/10000000000000000000 : ℝ) ≤ (5000330518131099/5000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (10002687668738903049/10000000000000000000 : ℝ)^1024 ≤ (5000330518131099/5000000000000000 : ℝ)^4163 := by
      have hnat : (10002687668738903049 : ℕ)^1024*5000000000000000^4163 ≤ 5000330518131099^4163*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002687668738903049 10000000000000000000 5000330518131099 5000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000330518131099/5000000000000000 : ℝ)) (X := (10002687668738903049/10000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012395546730955233/25000000000000000000 : ℝ) ≤ (1000121937716277/1000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (25012395546730955233/25000000000000000000 : ℝ)^1024 ≤ (1000121937716277/1000000000000000 : ℝ)^4163 := by
      have hnat : (25012395546730955233 : ℕ)^1024*1000000000000000^4163 ≤ 1000121937716277^4163*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012395546730955233 25000000000000000000 1000121937716277 1000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000121937716277/1000000000000000 : ℝ)) (X := (25012395546730955233/25000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036143843229305687/50000000000000000000 : ℝ) ≤ (5000888859031671/5000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50036143843229305687/50000000000000000000 : ℝ)^1024 ≤ (5000888859031671/5000000000000000 : ℝ)^4163 := by
      have hnat : (50036143843229305687 : ℕ)^1024*5000000000000000^4163 ≤ 5000888859031671^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036143843229305687 50000000000000000000 5000888859031671 5000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000888859031671/5000000000000000 : ℝ)) (X := (50036143843229305687/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2687668738903049/20000000000000000000 : ℝ) ≤ ((1024652350586849727/1025000000000000000 : ℝ)+2*(46528408381/25625000000000 : ℝ)*(279/2500 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (1024652350586849727/1025000000000000000 : ℝ)+2*(46528408381/25625000000000 : ℝ)*(279/2500 : ℝ)=(5000330518131099/5000000000000000 : ℝ) by norm_num, show 1+2*(2687668738903049/20000000000000000000 : ℝ)=(10002687668738903049/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36143843229305687/100000000000000000000 : ℝ)+(2687668738903049/20000000000000000000 : ℝ) ≤ ((1024652350586849727/1025000000000000000 : ℝ)+(46528408381/25625000000000 : ℝ)*((2847/20000 : ℝ)+(279/2500 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (1024652350586849727/1025000000000000000 : ℝ)+(46528408381/25625000000000 : ℝ)*((2847/20000 : ℝ)+(279/2500 : ℝ))=(1000121937716277/1000000000000000 : ℝ) by norm_num, show 1+(36143843229305687/100000000000000000000 : ℝ)+(2687668738903049/20000000000000000000 : ℝ)=(25012395546730955233/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36143843229305687/100000000000000000000 : ℝ) ≤ ((1024652350586849727/1025000000000000000 : ℝ)+2*(46528408381/25625000000000 : ℝ)*(2847/20000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (1024652350586849727/1025000000000000000 : ℝ)+2*(46528408381/25625000000000 : ℝ)*(2847/20000 : ℝ)=(5000888859031671/5000000000000000 : ℝ) by norm_num, show 1+2*(36143843229305687/100000000000000000000 : ℝ)=(50036143843229305687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1024652350586849727/1025000000000000000 : ℝ)*(X 1 0+X 2 0)+(46528408381/25625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1024652350586849727/1025000000000000000 : ℝ)) (alpha := (46528408381/25625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1024652350586849727/1025000000000000000 : ℝ)*(X 0 1+X 2 1)+(46528408381/25625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1024652350586849727/1025000000000000000 : ℝ)) (alpha := (46528408381/25625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1024652350586849727/1025000000000000000 : ℝ)*(X 0 2+X 1 2)+(46528408381/25625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (279/2500 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (1024652350586849727/1025000000000000000 : ℝ)) (alpha := (46528408381/25625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-542637623/2500000000 : ℝ)*X 0 0+(5395121343/10000000000 : ℝ)*X 0 1+(2631887897/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345273967/10000000000 : ℝ)*X 1 0+(-2237201651/10000000000 : ℝ)*X 1 1+(5263775811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672637137/5000000000 : ℝ)*X 2 0+(1315943887/2500000000 : ℝ)*X 2 1+(-223720159/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545713007/1250000000 : ℝ)*X 0 0+(4237197343/10000000000 : ℝ)*X 0 1+(4498096297/10000000000 : ℝ)*X 0 2+(545713007/1250000000 : ℝ)*X 1 0+(4237197343/10000000000 : ℝ)*X 1 1+(4498096297/10000000000 : ℝ)*X 1 2+(545713007/1250000000 : ℝ)*X 2 0+(4237197343/10000000000 : ℝ)*X 2 1+(4498096297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-108527801/500000000 : ℝ)*X 0 0+(5264115287/10000000000 : ℝ)*X 0 1+(2697390227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328004347/2500000000 : ℝ)*X 1 0+(-2106196827/10000000000 : ℝ)*X 1 1+(5394780443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656008691/5000000000 : ℝ)*X 2 0+(1078956089/2000000000 : ℝ)*X 2 1+(-65818651/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365714593/10000000000 : ℝ)*X 0 0+(4497421683/10000000000 : ℝ)*X 0 1+(4237874559/10000000000 : ℝ)*X 0 2+(4365714593/10000000000 : ℝ)*X 1 0+(4497421683/10000000000 : ℝ)*X 1 1+(4237874559/10000000000 : ℝ)*X 1 2+(4365714593/10000000000 : ℝ)*X 2 0+(4497421683/10000000000 : ℝ)*X 2 1+(4237874559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72092890209616549268509911/6406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1878956719/100000000000000 : ℝ)*(base19) + (92556091/5000000000000 : ℝ)*(base23) + (248615953/100000000000000 : ℝ)*(lower2) + (263430781/100000000000000 : ℝ)*(upper3) + (2345707/2500000000000 : ℝ)*(upper5) + (715409602854919/12500000000000 : ℝ)*(major0) + (715409602854919/12500000000000 : ℝ)*(major1) + (715409602854919/12500000000000 : ℝ)*(major2) + (3806775133011009/50000000000000 : ℝ)*(sp0) + (7613597196654543/100000000000000 : ℝ)*(sp1) + (3806798612244721/50000000000000 : ℝ)*(sp2) + (958230940660887/25000000000000 : ℝ)*(sp3) + (12202397311/25000000000000 : ℝ)*(sp4) + (7608076601/25000000000000 : ℝ)*(sp7) + (59889909296093/1562500000000 : ℝ)*(f.failure) + (3806799537805631/50000000000000 : ℝ)*(f.sum) + (6329566425237/1281250000000000000000000000 : ℝ)*base65 + (2827263449307887/12812500000000000000000000000000 : ℝ)*base68 + (247055788100067113/12812500000000000000000000000000 : ℝ)*base69 + (117239201562745387/12812500000000000000000000000000 : ℝ)*base72 + (15594598428927/5125000000000000000000000000 : ℝ)*base74 + (333573599817254613/12812500000000000000000000000000 : ℝ)*base75 + (152886312778817113/12812500000000000000000000000000 : ℝ)*base77 + (214564204808817113/12812500000000000000000000000000 : ℝ)*base79 + (4921989631263/1281250000000000000000000000 : ℝ)*base82 + (463647/78125000000000000000 : ℝ)*base90 + (463647/78125000000000000000 : ℝ)*base92 + (463647/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49020705654790887075605169/25625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (209450297/50000000000000 : ℝ)*(base19) + (27003619/6250000000000 : ℝ)*(base23) + (38379353/100000000000000 : ℝ)*(upper3) + (11002047/100000000000000 : ℝ)*(lower4) + (39250787/100000000000000 : ℝ)*(upper5) + (2876503376691349/50000000000000 : ℝ)*(major0) + (2876503376691349/50000000000000 : ℝ)*(major1) + (2876503376691349/50000000000000 : ℝ)*(major2) + (11153430439/100000000000000 : ℝ)*(sp1) + (18123893/160000000000 : ℝ)*(sp2) + (7653148720300483/100000000000000 : ℝ)*(sp4) + (153062742959389/2000000000000 : ℝ)*(sp5) + (3826568480404727/50000000000000 : ℝ)*(sp6) + (1926432361349069/50000000000000 : ℝ)*(sp7) + (1926432361349069/50000000000000 : ℝ)*(f.failure) + (7653148720300483/100000000000000 : ℝ)*(f.sum) + (3526976386999/2562500000000000000000000000 : ℝ)*base66 + (309928987931078277/51250000000000000000000000000000 : ℝ)*base68 + (198015416067328277/51250000000000000000000000000000 : ℝ)*base70 + (111191536621078277/51250000000000000000000000000000 : ℝ)*base72 + (10956979246623/5125000000000000000000000000 : ℝ)*base74 + (221946656461421723/51250000000000000000000000000000 : ℝ)*base75 + (128154136827328277/51250000000000000000000000000000 : ℝ)*base78 + (253986502982671723/51250000000000000000000000000000 : ℝ)*base79 + (764958627203/320312500000000000000000000 : ℝ)*base82 + (10987649/2500000000000000000000 : ℝ)*base89 + (10987649/2500000000000000000000 : ℝ)*base91 + (10987649/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1134_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (279/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1134_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1134_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1134_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1134_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1134_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
