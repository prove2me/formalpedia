-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1386_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:21.601554+00:00
-- url     : https://prove2.me/submissions/02c7bb9b-7867-4efc-9638-534c723562b1

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
theorem support_rectangle_w1386_s6_0 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-501639553/2500000000 : ℝ)*x 0 + (2705220843/5000000000 : ℝ)*x 1 + (2622929281/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (501639553/2500000000 : ℝ)^2173 ≤ (3057552290767/25000000000000 : ℝ)^1661 := by
    have hnat : (501639553 : ℕ)^2173*25000000000000^1661 ≤ 3057552290767^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501639553 2500000000 3057552290767 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705220843/5000000000 : ℝ)^2173 ≤ (22385780083813/50000000000000 : ℝ)^1661 := by
    have hnat : (2705220843 : ℕ)^2173*50000000000000^1661 ≤ 22385780083813^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705220843 5000000000 22385780083813 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622929281/5000000000 : ℝ)^2173 ≤ (4299823066209/10000000000000 : ℝ)^1661 := by
    have hnat : (2622929281 : ℕ)^2173*10000000000000^1661 ≤ 4299823066209^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622929281 5000000000 4299823066209 10000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-501639553/2500000000 : ℝ), (2705220843/5000000000 : ℝ), (2622929281/5000000000 : ℝ)] ![(3057552290767/25000000000000 : ℝ), (22385780083813/50000000000000 : ℝ), (4299823066209/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-501639553/2500000000 : ℝ)|^2173 ≤ (3057552290767/25000000000000 : ℝ)^1661
        have hw : |(-501639553/2500000000 : ℝ)|=(501639553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705220843/5000000000 : ℝ)|^2173 ≤ (22385780083813/50000000000000 : ℝ)^1661
        have hw : |(2705220843/5000000000 : ℝ)|=(2705220843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622929281/5000000000 : ℝ)|^2173 ≤ (4299823066209/10000000000000 : ℝ)^1661
        have hw : |(2622929281/5000000000 : ℝ)|=(2622929281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s6_1 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348195837/10000000000 : ℝ)*x 0 + (-1045190729/5000000000 : ℝ)*x 1 + (2622929249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348195837/10000000000 : ℝ)^2173 ≤ (22049448860173/50000000000000 : ℝ)^1661 := by
    have hnat : (5348195837 : ℕ)^2173*50000000000000^1661 ≤ 22049448860173^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348195837 10000000000 22049448860173 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1045190729/5000000000 : ℝ)^2173 ≤ (322571807183/2500000000000 : ℝ)^1661 := by
    have hnat : (1045190729 : ℕ)^2173*2500000000000^1661 ≤ 322571807183^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045190729 5000000000 322571807183 2500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622929249/5000000000 : ℝ)^2173 ≤ (8599645995161/20000000000000 : ℝ)^1661 := by
    have hnat : (2622929249 : ℕ)^2173*20000000000000^1661 ≤ 8599645995161^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622929249 5000000000 8599645995161 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348195837/10000000000 : ℝ), (-1045190729/5000000000 : ℝ), (2622929249/5000000000 : ℝ)] ![(22049448860173/50000000000000 : ℝ), (322571807183/2500000000000 : ℝ), (8599645995161/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348195837/10000000000 : ℝ)|^2173 ≤ (22049448860173/50000000000000 : ℝ)^1661
        have hw : |(5348195837/10000000000 : ℝ)|=(5348195837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1045190729/5000000000 : ℝ)|^2173 ≤ (322571807183/2500000000000 : ℝ)^1661
        have hw : |(-1045190729/5000000000 : ℝ)|=(1045190729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622929249/5000000000 : ℝ)|^2173 ≤ (8599645995161/20000000000000 : ℝ)^1661
        have hw : |(2622929249/5000000000 : ℝ)|=(2622929249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s6_2 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348196167/10000000000 : ℝ)*x 0 + (5245858271/10000000000 : ℝ)*x 1 + (-2090381319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348196167/10000000000 : ℝ)^2173 ≤ (5512362660017/12500000000000 : ℝ)^1661 := by
    have hnat : (5348196167 : ℕ)^2173*12500000000000^1661 ≤ 5512362660017^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348196167 10000000000 5512362660017 12500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245858271/10000000000 : ℝ)^2173 ≤ (42998227541641/100000000000000 : ℝ)^1661 := by
    have hnat : (5245858271 : ℕ)^2173*100000000000000^1661 ≤ 42998227541641^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245858271 10000000000 42998227541641 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2090381319/10000000000 : ℝ)^2173 ≤ (12902871164873/100000000000000 : ℝ)^1661 := by
    have hnat : (2090381319 : ℕ)^2173*100000000000000^1661 ≤ 12902871164873^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090381319 10000000000 12902871164873 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348196167/10000000000 : ℝ), (5245858271/10000000000 : ℝ), (-2090381319/10000000000 : ℝ)] ![(5512362660017/12500000000000 : ℝ), (42998227541641/100000000000000 : ℝ), (12902871164873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348196167/10000000000 : ℝ)|^2173 ≤ (5512362660017/12500000000000 : ℝ)^1661
        have hw : |(5348196167/10000000000 : ℝ)|=(5348196167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245858271/10000000000 : ℝ)|^2173 ≤ (42998227541641/100000000000000 : ℝ)^1661
        have hw : |(5245858271/10000000000 : ℝ)|=(5245858271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2090381319/10000000000 : ℝ)|^2173 ≤ (12902871164873/100000000000000 : ℝ)^1661
        have hw : |(-2090381319/10000000000 : ℝ)|=(2090381319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s6_3 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2157621927/5000000000 : ℝ)*x 0 + (4143281037/10000000000 : ℝ)*x 1 + (449372791/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157621927/5000000000 : ℝ)^2173 ≤ (16652002141571/50000000000000 : ℝ)^1661 := by
    have hnat : (2157621927 : ℕ)^2173*50000000000000^1661 ≤ 16652002141571^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157621927 5000000000 16652002141571 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4143281037/10000000000 : ℝ)^2173 ≤ (1263140154381/4000000000000 : ℝ)^1661 := by
    have hnat : (4143281037 : ℕ)^2173*4000000000000^1661 ≤ 1263140154381^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143281037 10000000000 1263140154381 4000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449372791/1000000000 : ℝ)^2173 ≤ (35117491850783/100000000000000 : ℝ)^1661 := by
    have hnat : (449372791 : ℕ)^2173*100000000000000^1661 ≤ 35117491850783^1661*1000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449372791 1000000000 35117491850783 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157621927/5000000000 : ℝ), (4143281037/10000000000 : ℝ), (449372791/1000000000 : ℝ)] ![(16652002141571/50000000000000 : ℝ), (1263140154381/4000000000000 : ℝ), (35117491850783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157621927/5000000000 : ℝ)|^2173 ≤ (16652002141571/50000000000000 : ℝ)^1661
        have hw : |(2157621927/5000000000 : ℝ)|=(2157621927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4143281037/10000000000 : ℝ)|^2173 ≤ (1263140154381/4000000000000 : ℝ)^1661
        have hw : |(4143281037/10000000000 : ℝ)|=(4143281037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449372791/1000000000 : ℝ)|^2173 ≤ (35117491850783/100000000000000 : ℝ)^1661
        have hw : |(449372791/1000000000 : ℝ)|=(449372791/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s6_4 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-31352659/156250000 : ℝ)*x 0 + (5246449817/10000000000 : ℝ)*x 1 + (5409847201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31352659/156250000 : ℝ)^2173 ≤ (12230304563209/100000000000000 : ℝ)^1661 := by
    have hnat : (31352659 : ℕ)^2173*100000000000000^1661 ≤ 12230304563209^1661*156250000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31352659 156250000 12230304563209 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246449817/10000000000 : ℝ)^2173 ≤ (21502285456699/50000000000000 : ℝ)^1661 := by
    have hnat : (5246449817 : ℕ)^2173*50000000000000^1661 ≤ 21502285456699^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246449817 10000000000 21502285456699 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409847201/10000000000 : ℝ)^2173 ≤ (11191281126699/25000000000000 : ℝ)^1661 := by
    have hnat : (5409847201 : ℕ)^2173*25000000000000^1661 ≤ 11191281126699^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409847201 10000000000 11191281126699 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31352659/156250000 : ℝ), (5246449817/10000000000 : ℝ), (5409847201/10000000000 : ℝ)] ![(12230304563209/100000000000000 : ℝ), (21502285456699/50000000000000 : ℝ), (11191281126699/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31352659/156250000 : ℝ)|^2173 ≤ (12230304563209/100000000000000 : ℝ)^1661
        have hw : |(-31352659/156250000 : ℝ)|=(31352659/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246449817/10000000000 : ℝ)|^2173 ≤ (21502285456699/50000000000000 : ℝ)^1661
        have hw : |(5246449817/10000000000 : ℝ)|=(5246449817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409847201/10000000000 : ℝ)|^2173 ≤ (11191281126699/25000000000000 : ℝ)^1661
        have hw : |(5409847201/10000000000 : ℝ)|=(5409847201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s6_5 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305595989/10000000000 : ℝ)*x 0 + (-385278521/2000000000 : ℝ)*x 1 + (1352461801/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305595989/10000000000 : ℝ)^2173 ≤ (43639927923331/100000000000000 : ℝ)^1661 := by
    have hnat : (5305595989 : ℕ)^2173*100000000000000^1661 ≤ 43639927923331^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305595989 10000000000 43639927923331 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (385278521/2000000000 : ℝ)^2173 ≤ (11594947518851/100000000000000 : ℝ)^1661 := by
    have hnat : (385278521 : ℕ)^2173*100000000000000^1661 ≤ 11594947518851^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385278521 2000000000 11594947518851 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1352461801/2500000000 : ℝ)^2173 ≤ (5595640567409/12500000000000 : ℝ)^1661 := by
    have hnat : (1352461801 : ℕ)^2173*12500000000000^1661 ≤ 5595640567409^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352461801 2500000000 5595640567409 12500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305595989/10000000000 : ℝ), (-385278521/2000000000 : ℝ), (1352461801/2500000000 : ℝ)] ![(43639927923331/100000000000000 : ℝ), (11594947518851/100000000000000 : ℝ), (5595640567409/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305595989/10000000000 : ℝ)|^2173 ≤ (43639927923331/100000000000000 : ℝ)^1661
        have hw : |(5305595989/10000000000 : ℝ)|=(5305595989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-385278521/2000000000 : ℝ)|^2173 ≤ (11594947518851/100000000000000 : ℝ)^1661
        have hw : |(-385278521/2000000000 : ℝ)|=(385278521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1352461801/2500000000 : ℝ)|^2173 ≤ (5595640567409/12500000000000 : ℝ)^1661
        have hw : |(1352461801/2500000000 : ℝ)|=(1352461801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s6_6 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (663199501/1250000000 : ℝ)*x 0 + (540984719/1000000000 : ℝ)*x 1 + (-1926392599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663199501/1250000000 : ℝ)^2173 ≤ (5454991015973/12500000000000 : ℝ)^1661 := by
    have hnat : (663199501 : ℕ)^2173*12500000000000^1661 ≤ 5454991015973^1661*1250000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663199501 1250000000 5454991015973 12500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540984719/1000000000 : ℝ)^2173 ≤ (11191281096929/25000000000000 : ℝ)^1661 := by
    have hnat : (540984719 : ℕ)^2173*25000000000000^1661 ≤ 11191281096929^1661*1000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540984719 1000000000 11191281096929 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926392599/10000000000 : ℝ)^2173 ≤ (2318989494321/20000000000000 : ℝ)^1661 := by
    have hnat : (1926392599 : ℕ)^2173*20000000000000^1661 ≤ 2318989494321^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926392599 10000000000 2318989494321 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663199501/1250000000 : ℝ), (540984719/1000000000 : ℝ), (-1926392599/10000000000 : ℝ)] ![(5454991015973/12500000000000 : ℝ), (11191281096929/25000000000000 : ℝ), (2318989494321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663199501/1250000000 : ℝ)|^2173 ≤ (5454991015973/12500000000000 : ℝ)^1661
        have hw : |(663199501/1250000000 : ℝ)|=(663199501/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540984719/1000000000 : ℝ)|^2173 ≤ (11191281096929/25000000000000 : ℝ)^1661
        have hw : |(540984719/1000000000 : ℝ)|=(540984719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926392599/10000000000 : ℝ)|^2173 ≤ (2318989494321/20000000000000 : ℝ)^1661
        have hw : |(-1926392599/10000000000 : ℝ)|=(1926392599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s6_7 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1078817207/2500000000 : ℝ)*x 0 + (4492468683/10000000000 : ℝ)*x 1 + (4144546773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078817207/2500000000 : ℝ)^2173 ≤ (33304256439371/100000000000000 : ℝ)^1661 := by
    have hnat : (1078817207 : ℕ)^2173*100000000000000^1661 ≤ 33304256439371^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078817207 2500000000 33304256439371 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492468683/10000000000 : ℝ)^2173 ≤ (35104618485863/100000000000000 : ℝ)^1661 := by
    have hnat : (4492468683 : ℕ)^2173*100000000000000^1661 ≤ 35104618485863^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492468683 10000000000 35104618485863 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4144546773/10000000000 : ℝ)^2173 ≤ (31591125064797/100000000000000 : ℝ)^1661 := by
    have hnat : (4144546773 : ℕ)^2173*100000000000000^1661 ≤ 31591125064797^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144546773 10000000000 31591125064797 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078817207/2500000000 : ℝ), (4492468683/10000000000 : ℝ), (4144546773/10000000000 : ℝ)] ![(33304256439371/100000000000000 : ℝ), (35104618485863/100000000000000 : ℝ), (31591125064797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078817207/2500000000 : ℝ)|^2173 ≤ (33304256439371/100000000000000 : ℝ)^1661
        have hw : |(1078817207/2500000000 : ℝ)|=(1078817207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492468683/10000000000 : ℝ)|^2173 ≤ (35104618485863/100000000000000 : ℝ)^1661
        have hw : |(4492468683/10000000000 : ℝ)|=(4492468683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4144546773/10000000000 : ℝ)|^2173 ≤ (31591125064797/100000000000000 : ℝ)^1661
        have hw : |(4144546773/10000000000 : ℝ)|=(4144546773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1386_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7367/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14739/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2811/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14739/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2811/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14739/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2811/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2811/25000 : ℝ) ^ (4345/1024 : ℝ) ≤ (9395099908965721/100000000000000000000 : ℝ) := by
    have hpowers : (2811/25000 : ℝ)^4345 ≤ (9395099908965721/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2811 : ℕ)^4345*100000000000000000000^1024 ≤ 9395099908965721^1024*25000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2811 25000 9395099908965721 100000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2811/25000 : ℝ)) (X := (9395099908965721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14739/100000 : ℝ) ^ (4345/1024 : ℝ) ≤ (14813012356851897/50000000000000000000 : ℝ) := by
    have hpowers : (14739/100000 : ℝ)^4345 ≤ (14813012356851897/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14739 : ℕ)^4345*50000000000000000000^1024 ≤ 14813012356851897^1024*100000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14739 100000 14813012356851897 50000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14739/100000 : ℝ)) (X := (14813012356851897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009395099908965721/50000000000000000000 : ℝ) ≤ (1250055350354063/1250000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (50009395099908965721/50000000000000000000 : ℝ)^1024 ≤ (1250055350354063/1250000000000000 : ℝ)^4345 := by
      have hnat : (50009395099908965721 : ℕ)^1024*1250000000000000^4345 ≤ 1250055350354063^4345*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009395099908965721 50000000000000000000 1250055350354063 1250000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250055350354063/1250000000000000 : ℝ)) (X := (50009395099908965721/50000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007804224924533903/20000000000000000000 : ℝ) ≤ (5000459743087693/5000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (20007804224924533903/20000000000000000000 : ℝ)^1024 ≤ (5000459743087693/5000000000000000 : ℝ)^4345 := by
      have hnat : (20007804224924533903 : ℕ)^1024*5000000000000000^4345 ≤ 5000459743087693^4345*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007804224924533903 20000000000000000000 5000459743087693 5000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000459743087693/5000000000000000 : ℝ)) (X := (20007804224924533903/20000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25014813012356851897/25000000000000000000 : ℝ) ≤ (2500349042379567/2500000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (25014813012356851897/25000000000000000000 : ℝ)^1024 ≤ (2500349042379567/2500000000000000 : ℝ)^4345 := by
      have hnat : (25014813012356851897 : ℕ)^1024*2500000000000000^4345 ≤ 2500349042379567^4345*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25014813012356851897 25000000000000000000 2500349042379567 2500000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500349042379567/2500000000000000 : ℝ)) (X := (25014813012356851897/25000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9395099908965721/100000000000000000000 : ℝ) ≤ ((1455867830870202961/1456250000000000000 : ℝ)+2*(238341671441/174750000000000 : ℝ)*(2811/25000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (1455867830870202961/1456250000000000000 : ℝ)+2*(238341671441/174750000000000 : ℝ)*(2811/25000 : ℝ)=(1250055350354063/1250000000000000 : ℝ) by norm_num, show 1+2*(9395099908965721/100000000000000000000 : ℝ)=(50009395099908965721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(14813012356851897/50000000000000000000 : ℝ)+(9395099908965721/100000000000000000000 : ℝ) ≤ ((1455867830870202961/1456250000000000000 : ℝ)+(238341671441/174750000000000 : ℝ)*((14739/100000 : ℝ)+(2811/25000 : ℝ)))^(4345/1024 : ℝ) := by
    rw [show (1455867830870202961/1456250000000000000 : ℝ)+(238341671441/174750000000000 : ℝ)*((14739/100000 : ℝ)+(2811/25000 : ℝ))=(5000459743087693/5000000000000000 : ℝ) by norm_num, show 1+(14813012356851897/50000000000000000000 : ℝ)+(9395099908965721/100000000000000000000 : ℝ)=(20007804224924533903/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(14813012356851897/50000000000000000000 : ℝ) ≤ ((1455867830870202961/1456250000000000000 : ℝ)+2*(238341671441/174750000000000 : ℝ)*(14739/100000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (1455867830870202961/1456250000000000000 : ℝ)+2*(238341671441/174750000000000 : ℝ)*(14739/100000 : ℝ)=(2500349042379567/2500000000000000 : ℝ) by norm_num, show 1+2*(14813012356851897/50000000000000000000 : ℝ)=(25014813012356851897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1455867830870202961/1456250000000000000 : ℝ)*(X 1 0+X 2 0)+(238341671441/174750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (1455867830870202961/1456250000000000000 : ℝ)) (alpha := (238341671441/174750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1455867830870202961/1456250000000000000 : ℝ)*(X 0 1+X 2 1)+(238341671441/174750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (1455867830870202961/1456250000000000000 : ℝ)) (alpha := (238341671441/174750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1455867830870202961/1456250000000000000 : ℝ)*(X 0 2+X 1 2)+(238341671441/174750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (2811/25000 : ℝ)) (hi := (14739/100000 : ℝ)) (c := (1455867830870202961/1456250000000000000 : ℝ)) (alpha := (238341671441/174750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-501639553/2500000000 : ℝ)*X 0 0+(2705220843/5000000000 : ℝ)*X 0 1+(2622929281/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348195837/10000000000 : ℝ)*X 1 0+(-1045190729/5000000000 : ℝ)*X 1 1+(2622929249/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348196167/10000000000 : ℝ)*X 2 0+(5245858271/10000000000 : ℝ)*X 2 1+(-2090381319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2157621927/5000000000 : ℝ)*X 0 0+(4143281037/10000000000 : ℝ)*X 0 1+(449372791/1000000000 : ℝ)*X 0 2+(2157621927/5000000000 : ℝ)*X 1 0+(4143281037/10000000000 : ℝ)*X 1 1+(449372791/1000000000 : ℝ)*X 1 2+(2157621927/5000000000 : ℝ)*X 2 0+(4143281037/10000000000 : ℝ)*X 2 1+(449372791/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-31352659/156250000 : ℝ)*X 0 0+(5246449817/10000000000 : ℝ)*X 0 1+(5409847201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305595989/10000000000 : ℝ)*X 1 0+(-385278521/2000000000 : ℝ)*X 1 1+(1352461801/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663199501/1250000000 : ℝ)*X 2 0+(540984719/1000000000 : ℝ)*X 2 1+(-1926392599/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078817207/2500000000 : ℝ)*X 0 0+(4492468683/10000000000 : ℝ)*X 0 1+(4144546773/10000000000 : ℝ)*X 0 2+(1078817207/2500000000 : ℝ)*X 1 0+(4492468683/10000000000 : ℝ)*X 1 1+(4144546773/10000000000 : ℝ)*X 1 2+(1078817207/2500000000 : ℝ)*X 2 0+(4492468683/10000000000 : ℝ)*X 2 1+(4144546773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (332196027098868739107017893/72812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (249730919/50000000000000 : ℝ)*(base19) + (280598887/50000000000000 : ℝ)*(base23) + (10468091/6250000000000 : ℝ)*(lower2) + (20661827/100000000000000 : ℝ)*(upper3) + (14799119/50000000000000 : ℝ)*(upper5) + (446473971452449/10000000000000 : ℝ)*(major0) + (446473971452449/10000000000000 : ℝ)*(major1) + (4464739714524491/100000000000000 : ℝ)*(major2) + (6075960725532313/100000000000000 : ℝ)*(sp0) + (75949638432211/1250000000000 : ℝ)*(sp1) + (379748188302559/6250000000000 : ℝ)*(sp2) + (1426751176789279/50000000000000 : ℝ)*(sp3) + (2169701281/20000000000000 : ℝ)*(sp4) + (1337338351/25000000000000 : ℝ)*(sp7) + (1426753851465981/50000000000000 : ℝ)*(f.failure) + (3037985787019359/50000000000000 : ℝ)*(f.sum) + (13122724834393/5825000000000000000000000000 : ℝ)*base66 + (33727757419605533/43687500000000000000000000000000 : ℝ)*base68 + (2168216132870221447/436875000000000000000000000000000 : ℝ)*base70 + (293340395149418033/43687500000000000000000000000000 : ℝ)*base72 + (41282372483357/5825000000000000000000000000 : ℝ)*base73 + (2790234358102096447/436875000000000000000000000000000 : ℝ)*base76 + (220935008610020533/43687500000000000000000000000000 : ℝ)*base78 + (1954241878145533/43687500000000000000000000000000 : ℝ)*base80 + (1786268142571/873750000000000000000000000 : ℝ)*base82 + (9991741/5000000000000000000000 : ℝ)*base89 + (9991741/5000000000000000000000 : ℝ)*base91 + (40008259/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (151047634747298171321300441/18203125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (703348079/50000000000000 : ℝ)*(base19) + (1539718701/100000000000000 : ℝ)*(base23) + (85218411/50000000000000 : ℝ)*(upper3) + (2474449/5000000000000 : ℝ)*(lower4) + (21803633/12500000000000 : ℝ)*(upper5) + (1124282052439273/25000000000000 : ℝ)*(major0) + (1124282052439273/25000000000000 : ℝ)*(major1) + (1124282052439273/25000000000000 : ℝ)*(major2) + (3636639331/12500000000000 : ℝ)*(sp1) + (7828347817/25000000000000 : ℝ)*(sp2) + (6120048281288433/100000000000000 : ℝ)*(sp4) + (6120017781477627/100000000000000 : ℝ)*(sp5) + (191250482130577/3125000000000 : ℝ)*(sp6) + (2874207861629219/100000000000000 : ℝ)*(sp7) + (2874207861629219/100000000000000 : ℝ)*(f.failure) + (6120048281288433/100000000000000 : ℝ)*(f.sum) + (11203162581811/4368750000000000000000000000 : ℝ)*base65 + (252616616600500441/109218750000000000000000000000000 : ℝ)*base68 + (168577740209187059/109218750000000000000000000000000 : ℝ)*base69 + (562163070489030809/109218750000000000000000000000000 : ℝ)*base71 + (11748495354703/8737500000000000000000000000 : ℝ)*base74 + (156332485997219191/109218750000000000000000000000000 : ℝ)*base76 + (289434787784187059/109218750000000000000000000000000 : ℝ)*base77 + (539347431544343309/109218750000000000000000000000000 : ℝ)*base79 + (4093475933119/17475000000000000000000000000 : ℝ)*base81 + (52704541/10000000000000000000000 : ℝ)*base90 + (52704541/10000000000000000000000 : ℝ)*base92 + (52704541/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1386_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1386_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1386_s7_0 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348185429/10000000000 : ℝ)*x 0 + (5245895489/10000000000 : ℝ)*x 1 + (-1633083/7812500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348185429/10000000000 : ℝ)^2173 ≤ (22049392723369/50000000000000 : ℝ)^1661 := by
    have hnat : (5348185429 : ℕ)^2173*50000000000000^1661 ≤ 22049392723369^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348185429 10000000000 22049392723369 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245895489/10000000000 : ℝ)^2173 ≤ (5374828329731/12500000000000 : ℝ)^1661 := by
    have hnat : (5245895489 : ℕ)^2173*12500000000000^1661 ≤ 5374828329731^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245895489 10000000000 5374828329731 12500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1633083/7812500 : ℝ)^2173 ≤ (3225646974299/25000000000000 : ℝ)^1661 := by
    have hnat : (1633083 : ℕ)^2173*25000000000000^1661 ≤ 3225646974299^1661*7812500^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633083 7812500 3225646974299 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348185429/10000000000 : ℝ), (5245895489/10000000000 : ℝ), (-1633083/7812500 : ℝ)] ![(22049392723369/50000000000000 : ℝ), (5374828329731/12500000000000 : ℝ), (3225646974299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348185429/10000000000 : ℝ)|^2173 ≤ (22049392723369/50000000000000 : ℝ)^1661
        have hw : |(5348185429/10000000000 : ℝ)|=(5348185429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245895489/10000000000 : ℝ)|^2173 ≤ (5374828329731/12500000000000 : ℝ)^1661
        have hw : |(5245895489/10000000000 : ℝ)|=(5245895489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1633083/7812500 : ℝ)|^2173 ≤ (3225646974299/25000000000000 : ℝ)^1661
        have hw : |(-1633083/7812500 : ℝ)|=(1633083/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s7_1 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1003286929/5000000000 : ℝ)*x 0 + (262324271/500000000 : ℝ)*x 1 + (5409809221/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1003286929/5000000000 : ℝ)^2173 ≤ (3057583480817/25000000000000 : ℝ)^1661 := by
    have hnat : (1003286929 : ℕ)^2173*25000000000000^1661 ≤ 3057583480817^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003286929 5000000000 3057583480817 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262324271/500000000 : ℝ)^2173 ≤ (21502476352441/50000000000000 : ℝ)^1661 := by
    have hnat : (262324271 : ℕ)^2173*50000000000000^1661 ≤ 21502476352441^1661*500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262324271 500000000 21502476352441 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409809221/10000000000 : ℝ)^2173 ≤ (44764713357659/100000000000000 : ℝ)^1661 := by
    have hnat : (5409809221 : ℕ)^2173*100000000000000^1661 ≤ 44764713357659^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409809221 10000000000 44764713357659 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1003286929/5000000000 : ℝ), (262324271/500000000 : ℝ), (5409809221/10000000000 : ℝ)] ![(3057583480817/25000000000000 : ℝ), (21502476352441/50000000000000 : ℝ), (44764713357659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1003286929/5000000000 : ℝ)|^2173 ≤ (3057583480817/25000000000000 : ℝ)^1661
        have hw : |(-1003286929/5000000000 : ℝ)|=(1003286929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262324271/500000000 : ℝ)|^2173 ≤ (21502476352441/50000000000000 : ℝ)^1661
        have hw : |(262324271/500000000 : ℝ)|=(262324271/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409809221/10000000000 : ℝ)|^2173 ≤ (44764713357659/100000000000000 : ℝ)^1661
        have hw : |(5409809221/10000000000 : ℝ)|=(5409809221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s7_2 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305605539/10000000000 : ℝ)*x 0 + (-1926431809/10000000000 : ℝ)*x 1 + (2704904597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305605539/10000000000 : ℝ)^2173 ≤ (43640030687907/100000000000000 : ℝ)^1661 := by
    have hnat : (5305605539 : ℕ)^2173*100000000000000^1661 ≤ 43640030687907^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305605539 10000000000 43640030687907 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1926431809/10000000000 : ℝ)^2173 ≤ (2319051245077/20000000000000 : ℝ)^1661 := by
    have hnat : (1926431809 : ℕ)^2173*20000000000000^1661 ≤ 2319051245077^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926431809 10000000000 2319051245077 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704904597/5000000000 : ℝ)^2173 ≤ (44764713065373/100000000000000 : ℝ)^1661 := by
    have hnat : (2704904597 : ℕ)^2173*100000000000000^1661 ≤ 44764713065373^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704904597 5000000000 44764713065373 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305605539/10000000000 : ℝ), (-1926431809/10000000000 : ℝ), (2704904597/5000000000 : ℝ)] ![(43640030687907/100000000000000 : ℝ), (2319051245077/20000000000000 : ℝ), (44764713065373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305605539/10000000000 : ℝ)|^2173 ≤ (43640030687907/100000000000000 : ℝ)^1661
        have hw : |(5305605539/10000000000 : ℝ)|=(5305605539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1926431809/10000000000 : ℝ)|^2173 ≤ (2319051245077/20000000000000 : ℝ)^1661
        have hw : |(-1926431809/10000000000 : ℝ)|=(1926431809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704904597/5000000000 : ℝ)|^2173 ≤ (44764713065373/100000000000000 : ℝ)^1661
        have hw : |(2704904597/5000000000 : ℝ)|=(2704904597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s7_3 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305605471/10000000000 : ℝ)*x 0 + (540980937/1000000000 : ℝ)*x 1 + (-1926431661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305605471/10000000000 : ℝ)^2173 ≤ (2182001497809/5000000000000 : ℝ)^1661 := by
    have hnat : (5305605471 : ℕ)^2173*5000000000000^1661 ≤ 2182001497809^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305605471 10000000000 2182001497809 5000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540980937/1000000000 : ℝ)^2173 ≤ (11191178742661/25000000000000 : ℝ)^1661 := by
    have hnat : (540980937 : ℕ)^2173*25000000000000^1661 ≤ 11191178742661^1661*1000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540980937 1000000000 11191178742661 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926431661/10000000000 : ℝ)^2173 ≤ (463810202399/4000000000000 : ℝ)^1661 := by
    have hnat : (1926431661 : ℕ)^2173*4000000000000^1661 ≤ 463810202399^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926431661 10000000000 463810202399 4000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305605471/10000000000 : ℝ), (540980937/1000000000 : ℝ), (-1926431661/10000000000 : ℝ)] ![(2182001497809/5000000000000 : ℝ), (11191178742661/25000000000000 : ℝ), (463810202399/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305605471/10000000000 : ℝ)|^2173 ≤ (2182001497809/5000000000000 : ℝ)^1661
        have hw : |(5305605471/10000000000 : ℝ)|=(5305605471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540980937/1000000000 : ℝ)|^2173 ≤ (11191178742661/25000000000000 : ℝ)^1661
        have hw : |(540980937/1000000000 : ℝ)|=(540980937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926431661/10000000000 : ℝ)|^2173 ≤ (463810202399/4000000000000 : ℝ)^1661
        have hw : |(-1926431661/10000000000 : ℝ)|=(1926431661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s7_4 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2157635731/5000000000 : ℝ)*x 0 + (4492389961/10000000000 : ℝ)*x 1 + (4144624807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157635731/5000000000 : ℝ)^2173 ≤ (8326070758559/25000000000000 : ℝ)^1661 := by
    have hnat : (2157635731 : ℕ)^2173*25000000000000^1661 ≤ 8326070758559^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157635731 5000000000 8326070758559 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492389961/10000000000 : ℝ)^2173 ≤ (35103813729833/100000000000000 : ℝ)^1661 := by
    have hnat : (4492389961 : ℕ)^2173*100000000000000^1661 ≤ 35103813729833^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492389961 10000000000 35103813729833 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4144624807/10000000000 : ℝ)^2173 ≤ (15795951607353/50000000000000 : ℝ)^1661 := by
    have hnat : (4144624807 : ℕ)^2173*50000000000000^1661 ≤ 15795951607353^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144624807 10000000000 15795951607353 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157635731/5000000000 : ℝ), (4492389961/10000000000 : ℝ), (4144624807/10000000000 : ℝ)] ![(8326070758559/25000000000000 : ℝ), (35103813729833/100000000000000 : ℝ), (15795951607353/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157635731/5000000000 : ℝ)|^2173 ≤ (8326070758559/25000000000000 : ℝ)^1661
        have hw : |(2157635731/5000000000 : ℝ)|=(2157635731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492389961/10000000000 : ℝ)|^2173 ≤ (35103813729833/100000000000000 : ℝ)^1661
        have hw : |(4492389961/10000000000 : ℝ)|=(4492389961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4144624807/10000000000 : ℝ)|^2173 ≤ (15795951607353/50000000000000 : ℝ)^1661
        have hw : |(4144624807/10000000000 : ℝ)|=(4144624807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1386_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11249/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14733/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7367/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7367/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11249/100000 : ℝ) ^ (4345/1024 : ℝ) ≤ (9412839906289713/100000000000000000000 : ℝ) := by
    have hpowers : (11249/100000 : ℝ)^4345 ≤ (9412839906289713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11249 : ℕ)^4345*100000000000000000000^1024 ≤ 9412839906289713^1024*100000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11249 100000 9412839906289713 100000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11249/100000 : ℝ)) (X := (9412839906289713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7367/50000 : ℝ) ^ (4345/1024 : ℝ) ≤ (29583403454113833/100000000000000000000 : ℝ) := by
    have hpowers : (7367/50000 : ℝ)^4345 ≤ (29583403454113833/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7367 : ℕ)^4345*100000000000000000000^1024 ≤ 29583403454113833^1024*50000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7367 50000 29583403454113833 100000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7367/50000 : ℝ)) (X := (29583403454113833/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009412839906289713/50000000000000000000 : ℝ) ≤ (2000088727776133/2000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (50009412839906289713/50000000000000000000 : ℝ)^1024 ≤ (2000088727776133/2000000000000000 : ℝ)^4345 := by
      have hnat : (50009412839906289713 : ℕ)^1024*2000000000000000^4345 ≤ 2000088727776133^4345*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009412839906289713 50000000000000000000 2000088727776133 2000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000088727776133/2000000000000000 : ℝ)) (X := (50009412839906289713/50000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019498121680201773/50000000000000000000 : ℝ) ≤ (10000918899965519/10000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (50019498121680201773/50000000000000000000 : ℝ)^1024 ≤ (10000918899965519/10000000000000000 : ℝ)^4345 := by
      have hnat : (50019498121680201773 : ℕ)^1024*10000000000000000^4345 ≤ 10000918899965519^4345*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019498121680201773 50000000000000000000 10000918899965519 10000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000918899965519/10000000000000000 : ℝ)) (X := (50019498121680201773/50000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50029583403454113833/50000000000000000000 : ℝ) ≤ (10001394161050373/10000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (50029583403454113833/50000000000000000000 : ℝ)^1024 ≤ (10001394161050373/10000000000000000 : ℝ)^4345 := by
      have hnat : (50029583403454113833 : ℕ)^1024*10000000000000000^4345 ≤ 10001394161050373^4345*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50029583403454113833 50000000000000000000 10001394161050373 10000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001394161050373/10000000000000000 : ℝ)) (X := (50029583403454113833/50000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9412839906289713/100000000000000000000 : ℝ) ≤ ((34840853657612072233/34850000000000000000 : ℝ)+2*(237630542427/174250000000000 : ℝ)*(11249/100000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (34840853657612072233/34850000000000000000 : ℝ)+2*(237630542427/174250000000000 : ℝ)*(11249/100000 : ℝ)=(2000088727776133/2000000000000000 : ℝ) by norm_num, show 1+2*(9412839906289713/100000000000000000000 : ℝ)=(50009412839906289713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(29583403454113833/100000000000000000000 : ℝ)+(9412839906289713/100000000000000000000 : ℝ) ≤ ((34840853657612072233/34850000000000000000 : ℝ)+(237630542427/174250000000000 : ℝ)*((7367/50000 : ℝ)+(11249/100000 : ℝ)))^(4345/1024 : ℝ) := by
    rw [show (34840853657612072233/34850000000000000000 : ℝ)+(237630542427/174250000000000 : ℝ)*((7367/50000 : ℝ)+(11249/100000 : ℝ))=(10000918899965519/10000000000000000 : ℝ) by norm_num, show 1+(29583403454113833/100000000000000000000 : ℝ)+(9412839906289713/100000000000000000000 : ℝ)=(50019498121680201773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(29583403454113833/100000000000000000000 : ℝ) ≤ ((34840853657612072233/34850000000000000000 : ℝ)+2*(237630542427/174250000000000 : ℝ)*(7367/50000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (34840853657612072233/34850000000000000000 : ℝ)+2*(237630542427/174250000000000 : ℝ)*(7367/50000 : ℝ)=(10001394161050373/10000000000000000 : ℝ) by norm_num, show 1+2*(29583403454113833/100000000000000000000 : ℝ)=(50029583403454113833/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34840853657612072233/34850000000000000000 : ℝ)*(X 1 0+X 2 0)+(237630542427/174250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (34840853657612072233/34850000000000000000 : ℝ)) (alpha := (237630542427/174250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34840853657612072233/34850000000000000000 : ℝ)*(X 0 1+X 2 1)+(237630542427/174250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (34840853657612072233/34850000000000000000 : ℝ)) (alpha := (237630542427/174250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34840853657612072233/34850000000000000000 : ℝ)*(X 0 2+X 1 2)+(237630542427/174250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (7367/50000 : ℝ)) (c := (34840853657612072233/34850000000000000000 : ℝ)) (alpha := (237630542427/174250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5348185429/10000000000 : ℝ)*X 2 0+(5245895489/10000000000 : ℝ)*X 2 1+(-1633083/7812500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s7_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1003286929/5000000000 : ℝ)*X 0 0+(262324271/500000000 : ℝ)*X 0 1+(5409809221/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s7_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5305605539/10000000000 : ℝ)*X 1 0+(-1926431809/10000000000 : ℝ)*X 1 1+(2704904597/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s7_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305605471/10000000000 : ℝ)*X 2 0+(540980937/1000000000 : ℝ)*X 2 1+(-1926431661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s7_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2157635731/5000000000 : ℝ)*X 0 0+(4492389961/10000000000 : ℝ)*X 0 1+(4144624807/10000000000 : ℝ)*X 0 2+(2157635731/5000000000 : ℝ)*X 1 0+(4492389961/10000000000 : ℝ)*X 1 1+(4144624807/10000000000 : ℝ)*X 1 2+(2157635731/5000000000 : ℝ)*X 2 0+(4492389961/10000000000 : ℝ)*X 2 1+(4144624807/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s7_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11836593648142204824424576743/1742500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483138829/50000000000000 : ℝ)*(base19) + (516766019/50000000000000 : ℝ)*(base23) + (291621423/100000000000000 : ℝ)*(lower1) + (6769347/5000000000000 : ℝ)*(upper3) + (24599693/50000000000000 : ℝ)*(lower4) + (19882683/12500000000000 : ℝ)*(upper5) + (4499141405254843/100000000000000 : ℝ)*(major0) + (4499141405254843/100000000000000 : ℝ)*(major1) + (4499141405254843/100000000000000 : ℝ)*(major2) + (1650899019/25000000000000 : ℝ)*(sp0) + (3061394023738079/50000000000000 : ℝ)*(sp1) + (6122787081198501/100000000000000 : ℝ)*(sp2) + (1224556082069609/20000000000000 : ℝ)*(sp3) + (359436817075521/12500000000000 : ℝ)*(sp4) + (359436817075521/12500000000000 : ℝ)*(f.failure) + (3061394023738079/50000000000000 : ℝ)*(f.sum) + (10487952370911/8712500000000000000000000000 : ℝ)*base65 + (59034410035398725581/3485000000000000000000000000000000 : ℝ)*base68 + (34678373683891274419/3485000000000000000000000000000000 : ℝ)*base69 + (73862655847193725581/3485000000000000000000000000000000 : ℝ)*base72 + (123001665450847/17425000000000000000000000000 : ℝ)*base73 + (313747536697031274419/3485000000000000000000000000000000 : ℝ)*base75 + (11286928499206274419/3485000000000000000000000000000000 : ℝ)*base77 + (30446218372411274419/3485000000000000000000000000000000 : ℝ)*base79 + (2199563750253/17425000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (10180319/1250000000000000000000 : ℝ)*base90 + (10180319/1250000000000000000000 : ℝ)*base92 + (10180319/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1386_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1386_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1386_s8_0 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2006565161/10000000000 : ℝ)*x 0 + (2705198917/5000000000 : ℝ)*x 1 + (1049179533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2006565161/10000000000 : ℝ)^2173 ≤ (12230264573911/100000000000000 : ℝ)^1661 := by
    have hnat : (2006565161 : ℕ)^2173*100000000000000^1661 ≤ 12230264573911^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006565161 10000000000 12230264573911 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705198917/5000000000 : ℝ)^2173 ≤ (5596385679459/12500000000000 : ℝ)^1661 := by
    have hnat : (2705198917 : ℕ)^2173*12500000000000^1661 ≤ 5596385679459^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705198917 5000000000 5596385679459 12500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049179533/2000000000 : ℝ)^2173 ≤ (42998649971567/100000000000000 : ℝ)^1661 := by
    have hnat : (1049179533 : ℕ)^2173*100000000000000^1661 ≤ 42998649971567^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049179533 2000000000 42998649971567 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2006565161/10000000000 : ℝ), (2705198917/5000000000 : ℝ), (1049179533/2000000000 : ℝ)] ![(12230264573911/100000000000000 : ℝ), (5596385679459/12500000000000 : ℝ), (42998649971567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2006565161/10000000000 : ℝ)|^2173 ≤ (12230264573911/100000000000000 : ℝ)^1661
        have hw : |(-2006565161/10000000000 : ℝ)|=(2006565161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705198917/5000000000 : ℝ)|^2173 ≤ (5596385679459/12500000000000 : ℝ)^1661
        have hw : |(2705198917/5000000000 : ℝ)|=(2705198917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049179533/2000000000 : ℝ)|^2173 ≤ (42998649971567/100000000000000 : ℝ)^1661
        have hw : |(1049179533/2000000000 : ℝ)|=(1049179533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s8_1 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5348184427/10000000000 : ℝ)*x 0 + (-2090344927/10000000000 : ℝ)*x 1 + (5245897487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348184427/10000000000 : ℝ)^2173 ≤ (1763950985517/4000000000000 : ℝ)^1661 := by
    have hnat : (5348184427 : ℕ)^2173*4000000000000^1661 ≤ 1763950985517^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348184427 10000000000 1763950985517 4000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2090344927/10000000000 : ℝ)^2173 ≤ (3225644323643/25000000000000 : ℝ)^1661 := by
    have hnat : (2090344927 : ℕ)^2173*25000000000000^1661 ≤ 3225644323643^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090344927 10000000000 3225644323643 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245897487/10000000000 : ℝ)^2173 ≤ (8599729612567/20000000000000 : ℝ)^1661 := by
    have hnat : (5245897487 : ℕ)^2173*20000000000000^1661 ≤ 8599729612567^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245897487 10000000000 8599729612567 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348184427/10000000000 : ℝ), (-2090344927/10000000000 : ℝ), (5245897487/10000000000 : ℝ)] ![(1763950985517/4000000000000 : ℝ), (3225644323643/25000000000000 : ℝ), (8599729612567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348184427/10000000000 : ℝ)|^2173 ≤ (1763950985517/4000000000000 : ℝ)^1661
        have hw : |(5348184427/10000000000 : ℝ)|=(5348184427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2090344927/10000000000 : ℝ)|^2173 ≤ (3225644323643/25000000000000 : ℝ)^1661
        have hw : |(-2090344927/10000000000 : ℝ)|=(2090344927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245897487/10000000000 : ℝ)|^2173 ≤ (8599729612567/20000000000000 : ℝ)^1661
        have hw : |(5245897487/10000000000 : ℝ)|=(5245897487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s8_2 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674092193/5000000000 : ℝ)*x 0 + (262294873/500000000 : ℝ)*x 1 + (-2090345017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674092193/5000000000 : ℝ)^2173 ≤ (44098774195649/100000000000000 : ℝ)^1661 := by
    have hnat : (2674092193 : ℕ)^2173*100000000000000^1661 ≤ 44098774195649^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674092193 5000000000 44098774195649 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262294873/500000000 : ℝ)^2173 ≤ (10749661943327/25000000000000 : ℝ)^1661 := by
    have hnat : (262294873 : ℕ)^2173*25000000000000^1661 ≤ 10749661943327^1661*500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262294873 500000000 10749661943327 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2090345017/10000000000 : ℝ)^2173 ≤ (3225644505333/25000000000000 : ℝ)^1661 := by
    have hnat : (2090345017 : ℕ)^2173*25000000000000^1661 ≤ 3225644505333^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090345017 10000000000 3225644505333 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674092193/5000000000 : ℝ), (262294873/500000000 : ℝ), (-2090345017/10000000000 : ℝ)] ![(44098774195649/100000000000000 : ℝ), (10749661943327/25000000000000 : ℝ), (3225644505333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674092193/5000000000 : ℝ)|^2173 ≤ (44098774195649/100000000000000 : ℝ)^1661
        have hw : |(2674092193/5000000000 : ℝ)|=(2674092193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262294873/500000000 : ℝ)|^2173 ≤ (10749661943327/25000000000000 : ℝ)^1661
        have hw : |(262294873/500000000 : ℝ)|=(262294873/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2090345017/10000000000 : ℝ)|^2173 ≤ (3225644505333/25000000000000 : ℝ)^1661
        have hw : |(-2090345017/10000000000 : ℝ)|=(2090345017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s8_3 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4315246719/10000000000 : ℝ)*x 0 + (2071684459/5000000000 : ℝ)*x 1 + (449363937/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315246719/10000000000 : ℝ)^2173 ≤ (8326008302577/25000000000000 : ℝ)^1661 := by
    have hnat : (4315246719 : ℕ)^2173*25000000000000^1661 ≤ 8326008302577^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315246719 10000000000 8326008302577 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2071684459/5000000000 : ℝ)^2173 ≤ (6315876024177/20000000000000 : ℝ)^1661 := by
    have hnat : (2071684459 : ℕ)^2173*20000000000000^1661 ≤ 6315876024177^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071684459 5000000000 6315876024177 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449363937/1000000000 : ℝ)^2173 ≤ (7023317329963/20000000000000 : ℝ)^1661 := by
    have hnat : (449363937 : ℕ)^2173*20000000000000^1661 ≤ 7023317329963^1661*1000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449363937 1000000000 7023317329963 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315246719/10000000000 : ℝ), (2071684459/5000000000 : ℝ), (449363937/1000000000 : ℝ)] ![(8326008302577/25000000000000 : ℝ), (6315876024177/20000000000000 : ℝ), (7023317329963/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315246719/10000000000 : ℝ)|^2173 ≤ (8326008302577/25000000000000 : ℝ)^1661
        have hw : |(4315246719/10000000000 : ℝ)|=(4315246719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2071684459/5000000000 : ℝ)|^2173 ≤ (6315876024177/20000000000000 : ℝ)^1661
        have hw : |(2071684459/5000000000 : ℝ)|=(2071684459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449363937/1000000000 : ℝ)|^2173 ≤ (7023317329963/20000000000000 : ℝ)^1661
        have hw : |(449363937/1000000000 : ℝ)|=(449363937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s8_4 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2006576993/10000000000 : ℝ)*x 0 + (1311622147/2500000000 : ℝ)*x 1 + (2704901887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2006576993/10000000000 : ℝ)^2173 ≤ (12230358921593/100000000000000 : ℝ)^1661 := by
    have hnat : (2006576993 : ℕ)^2173*100000000000000^1661 ≤ 12230358921593^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006576993 10000000000 12230358921593 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311622147/2500000000 : ℝ)^2173 ≤ (43004986677211/100000000000000 : ℝ)^1661 := by
    have hnat : (1311622147 : ℕ)^2173*100000000000000^1661 ≤ 43004986677211^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311622147 2500000000 43004986677211 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2704901887/5000000000 : ℝ)^2173 ≤ (8952930878343/20000000000000 : ℝ)^1661 := by
    have hnat : (2704901887 : ℕ)^2173*20000000000000^1661 ≤ 8952930878343^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704901887 5000000000 8952930878343 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2006576993/10000000000 : ℝ), (1311622147/2500000000 : ℝ), (2704901887/5000000000 : ℝ)] ![(12230358921593/100000000000000 : ℝ), (43004986677211/100000000000000 : ℝ), (8952930878343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2006576993/10000000000 : ℝ)|^2173 ≤ (12230358921593/100000000000000 : ℝ)^1661
        have hw : |(-2006576993/10000000000 : ℝ)|=(2006576993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311622147/2500000000 : ℝ)|^2173 ≤ (43004986677211/100000000000000 : ℝ)^1661
        have hw : |(1311622147/2500000000 : ℝ)|=(1311622147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2704901887/5000000000 : ℝ)|^2173 ≤ (8952930878343/20000000000000 : ℝ)^1661
        have hw : |(2704901887/5000000000 : ℝ)|=(2704901887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s8_5 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4315272437/10000000000 : ℝ)*x 0 + (898476109/2000000000 : ℝ)*x 1 + (4144633473/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4315272437/10000000000 : ℝ)^2173 ≤ (16652146439289/50000000000000 : ℝ)^1661 := by
    have hnat : (4315272437 : ℕ)^2173*50000000000000^1661 ≤ 16652146439289^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4315272437 10000000000 16652146439289 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898476109/2000000000 : ℝ)^2173 ≤ (17551858736313/50000000000000 : ℝ)^1661 := by
    have hnat : (898476109 : ℕ)^2173*50000000000000^1661 ≤ 17551858736313^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898476109 2000000000 17551858736313 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4144633473/10000000000 : ℝ)^2173 ≤ (15795994815883/50000000000000 : ℝ)^1661 := by
    have hnat : (4144633473 : ℕ)^2173*50000000000000^1661 ≤ 15795994815883^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144633473 10000000000 15795994815883 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4315272437/10000000000 : ℝ), (898476109/2000000000 : ℝ), (4144633473/10000000000 : ℝ)] ![(16652146439289/50000000000000 : ℝ), (17551858736313/50000000000000 : ℝ), (15795994815883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4315272437/10000000000 : ℝ)|^2173 ≤ (16652146439289/50000000000000 : ℝ)^1661
        have hw : |(4315272437/10000000000 : ℝ)|=(4315272437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898476109/2000000000 : ℝ)|^2173 ≤ (17551858736313/50000000000000 : ℝ)^1661
        have hw : |(898476109/2000000000 : ℝ)|=(898476109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4144633473/10000000000 : ℝ)|^2173 ≤ (15795994815883/50000000000000 : ℝ)^1661
        have hw : |(4144633473/10000000000 : ℝ)|=(4144633473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1386_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9/80 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14733/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11249/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14733/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11249/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14733/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11249/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11249/100000 : ℝ) ^ (4345/1024 : ℝ) ≤ (9412839906289713/100000000000000000000 : ℝ) := by
    have hpowers : (11249/100000 : ℝ)^4345 ≤ (9412839906289713/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11249 : ℕ)^4345*100000000000000000000^1024 ≤ 9412839906289713^1024*100000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11249 100000 9412839906289713 100000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11249/100000 : ℝ)) (X := (9412839906289713/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14733/100000 : ℝ) ^ (4345/1024 : ℝ) ≤ (1478744241458527/5000000000000000000 : ℝ) := by
    have hpowers : (14733/100000 : ℝ)^4345 ≤ (1478744241458527/5000000000000000000 : ℝ)^1024 := by
      have hnat : (14733 : ℕ)^4345*5000000000000000000^1024 ≤ 1478744241458527^1024*100000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14733 100000 1478744241458527 5000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14733/100000 : ℝ)) (X := (1478744241458527/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009412839906289713/50000000000000000000 : ℝ) ≤ (2000088727776133/2000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (50009412839906289713/50000000000000000000 : ℝ)^1024 ≤ (2000088727776133/2000000000000000 : ℝ)^4345 := by
      have hnat : (50009412839906289713 : ℕ)^1024*2000000000000000^4345 ≤ 2000088727776133^4345*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009412839906289713 50000000000000000000 2000088727776133 2000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000088727776133/2000000000000000 : ℝ)) (X := (50009412839906289713/50000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100038987724735460253/100000000000000000000 : ℝ) ≤ (10000918699264181/10000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (100038987724735460253/100000000000000000000 : ℝ)^1024 ≤ (10000918699264181/10000000000000000 : ℝ)^4345 := by
      have hnat : (100038987724735460253 : ℕ)^1024*10000000000000000^4345 ≤ 10000918699264181^4345*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100038987724735460253 100000000000000000000 10000918699264181 10000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000918699264181/10000000000000000 : ℝ)) (X := (100038987724735460253/100000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501478744241458527/2500000000000000000 : ℝ) ≤ (10001393759647697/10000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (2501478744241458527/2500000000000000000 : ℝ)^1024 ≤ (10001393759647697/10000000000000000 : ℝ)^4345 := by
      have hnat : (2501478744241458527 : ℕ)^1024*10000000000000000^4345 ≤ 10001393759647697^4345*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501478744241458527 2500000000000000000 10001393759647697 10000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001393759647697/10000000000000000 : ℝ)) (X := (2501478744241458527/2500000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9412839906289713/100000000000000000000 : ℝ) ≤ ((8707714432337973473/8710000000000000000 : ℝ)+2*(118765095879/87100000000000 : ℝ)*(11249/100000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (8707714432337973473/8710000000000000000 : ℝ)+2*(118765095879/87100000000000 : ℝ)*(11249/100000 : ℝ)=(2000088727776133/2000000000000000 : ℝ) by norm_num, show 1+2*(9412839906289713/100000000000000000000 : ℝ)=(50009412839906289713/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1478744241458527/5000000000000000000 : ℝ)+(9412839906289713/100000000000000000000 : ℝ) ≤ ((8707714432337973473/8710000000000000000 : ℝ)+(118765095879/87100000000000 : ℝ)*((14733/100000 : ℝ)+(11249/100000 : ℝ)))^(4345/1024 : ℝ) := by
    rw [show (8707714432337973473/8710000000000000000 : ℝ)+(118765095879/87100000000000 : ℝ)*((14733/100000 : ℝ)+(11249/100000 : ℝ))=(10000918699264181/10000000000000000 : ℝ) by norm_num, show 1+(1478744241458527/5000000000000000000 : ℝ)+(9412839906289713/100000000000000000000 : ℝ)=(100038987724735460253/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1478744241458527/5000000000000000000 : ℝ) ≤ ((8707714432337973473/8710000000000000000 : ℝ)+2*(118765095879/87100000000000 : ℝ)*(14733/100000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (8707714432337973473/8710000000000000000 : ℝ)+2*(118765095879/87100000000000 : ℝ)*(14733/100000 : ℝ)=(10001393759647697/10000000000000000 : ℝ) by norm_num, show 1+2*(1478744241458527/5000000000000000000 : ℝ)=(2501478744241458527/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8707714432337973473/8710000000000000000 : ℝ)*(X 1 0+X 2 0)+(118765095879/87100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (8707714432337973473/8710000000000000000 : ℝ)) (alpha := (118765095879/87100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8707714432337973473/8710000000000000000 : ℝ)*(X 0 1+X 2 1)+(118765095879/87100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (8707714432337973473/8710000000000000000 : ℝ)) (alpha := (118765095879/87100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8707714432337973473/8710000000000000000 : ℝ)*(X 0 2+X 1 2)+(118765095879/87100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (11249/100000 : ℝ)) (hi := (14733/100000 : ℝ)) (c := (8707714432337973473/8710000000000000000 : ℝ)) (alpha := (118765095879/87100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2006565161/10000000000 : ℝ)*X 0 0+(2705198917/5000000000 : ℝ)*X 0 1+(1049179533/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348184427/10000000000 : ℝ)*X 1 0+(-2090344927/10000000000 : ℝ)*X 1 1+(5245897487/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674092193/5000000000 : ℝ)*X 2 0+(262294873/500000000 : ℝ)*X 2 1+(-2090345017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4315246719/10000000000 : ℝ)*X 0 0+(2071684459/5000000000 : ℝ)*X 0 1+(449363937/1000000000 : ℝ)*X 0 2+(4315246719/10000000000 : ℝ)*X 1 0+(2071684459/5000000000 : ℝ)*X 1 1+(449363937/1000000000 : ℝ)*X 1 2+(4315246719/10000000000 : ℝ)*X 2 0+(2071684459/5000000000 : ℝ)*X 2 1+(449363937/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2006576993/10000000000 : ℝ)*X 0 0+(1311622147/2500000000 : ℝ)*X 0 1+(2704901887/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4315272437/10000000000 : ℝ)*X 0 0+(898476109/2000000000 : ℝ)*X 0 1+(4144633473/10000000000 : ℝ)*X 0 2+(4315272437/10000000000 : ℝ)*X 1 0+(898476109/2000000000 : ℝ)*X 1 1+(4144633473/10000000000 : ℝ)*X 1 2+(4315272437/10000000000 : ℝ)*X 2 0+(898476109/2000000000 : ℝ)*X 2 1+(4144633473/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s8_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (247413780164399605015722471/217750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (96617799/12500000000000 : ℝ)*(base19) + (693920857/100000000000000 : ℝ)*(base23) + (49407941/100000000000000 : ℝ)*(upper2) + (17981197/12500000000000 : ℝ)*(upper3) + (16686513/25000000000000 : ℝ)*(upper4) + (223349740647731/5000000000000 : ℝ)*(major0) + (223349740647731/5000000000000 : ℝ)*(major1) + (2233497406477311/50000000000000 : ℝ)*(major2) + (303951678191533/5000000000000 : ℝ)*(sp0) + (379939989500441/6250000000000 : ℝ)*(sp1) + (6079039911028591/100000000000000 : ℝ)*(sp2) + (2854941824322243/100000000000000 : ℝ)*(sp3) + (1760279697/25000000000000 : ℝ)*(sp4) + (1431752651/20000000000000 : ℝ)*(sp5) + (1427474491542749/50000000000000 : ℝ)*(f.failure) + (759880075618681/12500000000000 : ℝ)*(f.sum) + (22399039670019/4355000000000000000000000000 : ℝ)*base65 + (291808473247820237/43550000000000000000000000000000 : ℝ)*base68 + (3330566547279871103/435500000000000000000000000000000 : ℝ)*base69 + (334378216357870237/43550000000000000000000000000000 : ℝ)*base72 + (117075203111/272187500000000000000000000 : ℝ)*base74 + (4644664515449871103/435500000000000000000000000000000 : ℝ)*base75 + (184554640286360237/43550000000000000000000000000000 : ℝ)*base78 + (724711501866410237/43550000000000000000000000000000 : ℝ)*base80 + (332876012929/435500000000000000000000000 : ℝ)*base81 + (52117789/5000000000000000000000 : ℝ)*base89 + (52117789/5000000000000000000000 : ℝ)*base91 + (47882211/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1386_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11249/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1386_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1386_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1386_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1386_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1386_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14739/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2811/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14733/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1386_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
