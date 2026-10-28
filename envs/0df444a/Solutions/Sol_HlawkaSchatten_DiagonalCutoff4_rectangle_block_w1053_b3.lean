-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1053_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:57:11.105037+00:00
-- url     : https://prove2.me/submissions/c013072b-21c3-4964-a054-58e0755937fc

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
theorem support_rectangle_w1053_s9_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210188049/10000000000 : ℝ)*x 0 + (5394559443/10000000000 : ℝ)*x 1 + (5264233497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210188049/10000000000 : ℝ)^4123 ≤ (6710880778689/50000000000000 : ℝ)^3099 := by
    have hnat : (2210188049 : ℕ)^4123*50000000000000^3099 ≤ 6710880778689^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210188049 10000000000 6710880778689 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394559443/10000000000 : ℝ)^4123 ≤ (43993287892607/100000000000000 : ℝ)^3099 := by
    have hnat : (5394559443 : ℕ)^4123*100000000000000^3099 ≤ 43993287892607^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394559443 10000000000 43993287892607 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264233497/10000000000 : ℝ)^4123 ≤ (10646237634647/25000000000000 : ℝ)^3099 := by
    have hnat : (5264233497 : ℕ)^4123*25000000000000^3099 ≤ 10646237634647^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264233497 10000000000 10646237634647 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210188049/10000000000 : ℝ), (5394559443/10000000000 : ℝ), (5264233497/10000000000 : ℝ)] ![(6710880778689/50000000000000 : ℝ), (43993287892607/100000000000000 : ℝ), (10646237634647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210188049/10000000000 : ℝ)|^4123 ≤ (6710880778689/50000000000000 : ℝ)^3099
        have hw : |(-2210188049/10000000000 : ℝ)|=(2210188049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394559443/10000000000 : ℝ)|^4123 ≤ (43993287892607/100000000000000 : ℝ)^3099
        have hw : |(5394559443/10000000000 : ℝ)|=(5394559443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264233497/10000000000 : ℝ)|^4123 ≤ (10646237634647/25000000000000 : ℝ)^3099
        have hw : |(5264233497/10000000000 : ℝ)|=(5264233497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s9_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334062569/625000000 : ℝ)*x 0 + (-569078653/2500000000 : ℝ)*x 1 + (526423379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334062569/625000000 : ℝ)^4123 ≤ (43456407040741/100000000000000 : ℝ)^3099 := by
    have hnat : (334062569 : ℕ)^4123*100000000000000^3099 ≤ 43456407040741^3099*625000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334062569 625000000 43456407040741 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (569078653/2500000000 : ℝ)^4123 ≤ (13958639255641/100000000000000 : ℝ)^3099 := by
    have hnat : (569078653 : ℕ)^4123*100000000000000^3099 ≤ 13958639255641^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      569078653 2500000000 13958639255641 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526423379/1000000000 : ℝ)^4123 ≤ (21292476845999/50000000000000 : ℝ)^3099 := by
    have hnat : (526423379 : ℕ)^4123*50000000000000^3099 ≤ 21292476845999^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526423379 1000000000 21292476845999 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334062569/625000000 : ℝ), (-569078653/2500000000 : ℝ), (526423379/1000000000 : ℝ)] ![(43456407040741/100000000000000 : ℝ), (13958639255641/100000000000000 : ℝ), (21292476845999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334062569/625000000 : ℝ)|^4123 ≤ (43456407040741/100000000000000 : ℝ)^3099
        have hw : |(334062569/625000000 : ℝ)|=(334062569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-569078653/2500000000 : ℝ)|^4123 ≤ (13958639255641/100000000000000 : ℝ)^3099
        have hw : |(-569078653/2500000000 : ℝ)|=(569078653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526423379/1000000000 : ℝ)|^4123 ≤ (21292476845999/50000000000000 : ℝ)^3099
        have hw : |(526423379/1000000000 : ℝ)|=(526423379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s9_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534500159/1000000000 : ℝ)*x 0 + (1316058361/2500000000 : ℝ)*x 1 + (-2276314423/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534500159/1000000000 : ℝ)^4123 ≤ (21728206148847/50000000000000 : ℝ)^3099 := by
    have hnat : (534500159 : ℕ)^4123*50000000000000^3099 ≤ 21728206148847^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534500159 1000000000 21728206148847 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316058361/2500000000 : ℝ)^4123 ≤ (2661559373011/6250000000000 : ℝ)^3099 := by
    have hnat : (1316058361 : ℕ)^4123*6250000000000^3099 ≤ 2661559373011^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316058361 2500000000 2661559373011 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276314423/10000000000 : ℝ)^4123 ≤ (872414857107/6250000000000 : ℝ)^3099 := by
    have hnat : (2276314423 : ℕ)^4123*6250000000000^3099 ≤ 872414857107^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276314423 10000000000 872414857107 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534500159/1000000000 : ℝ), (1316058361/2500000000 : ℝ), (-2276314423/10000000000 : ℝ)] ![(21728206148847/50000000000000 : ℝ), (2661559373011/6250000000000 : ℝ), (872414857107/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534500159/1000000000 : ℝ)|^4123 ≤ (21728206148847/50000000000000 : ℝ)^3099
        have hw : |(534500159/1000000000 : ℝ)|=(534500159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316058361/2500000000 : ℝ)|^4123 ≤ (2661559373011/6250000000000 : ℝ)^3099
        have hw : |(1316058361/2500000000 : ℝ)|=(1316058361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2276314423/10000000000 : ℝ)|^4123 ≤ (872414857107/6250000000000 : ℝ)^3099
        have hw : |(-2276314423/10000000000 : ℝ)|=(2276314423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s9_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4377366399/10000000000 : ℝ)*x 0 + (4251869469/10000000000 : ℝ)*x 1 + (2253315049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4377366399/10000000000 : ℝ)^4123 ≤ (33316485025887/100000000000000 : ℝ)^3099 := by
    have hnat : (4377366399 : ℕ)^4123*100000000000000^3099 ≤ 33316485025887^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4377366399 10000000000 33316485025887 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4251869469/10000000000 : ℝ)^4123 ≤ (32051760982939/100000000000000 : ℝ)^3099 := by
    have hnat : (4251869469 : ℕ)^4123*100000000000000^3099 ≤ 32051760982939^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4251869469 10000000000 32051760982939 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253315049/5000000000 : ℝ)^4123 ≤ (34631753967379/100000000000000 : ℝ)^3099 := by
    have hnat : (2253315049 : ℕ)^4123*100000000000000^3099 ≤ 34631753967379^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253315049 5000000000 34631753967379 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4377366399/10000000000 : ℝ), (4251869469/10000000000 : ℝ), (2253315049/5000000000 : ℝ)] ![(33316485025887/100000000000000 : ℝ), (32051760982939/100000000000000 : ℝ), (34631753967379/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4377366399/10000000000 : ℝ)|^4123 ≤ (33316485025887/100000000000000 : ℝ)^3099
        have hw : |(4377366399/10000000000 : ℝ)|=(4377366399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4251869469/10000000000 : ℝ)|^4123 ≤ (32051760982939/100000000000000 : ℝ)^3099
        have hw : |(4251869469/10000000000 : ℝ)|=(4251869469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253315049/5000000000 : ℝ)|^4123 ≤ (34631753967379/100000000000000 : ℝ)^3099
        have hw : |(2253315049/5000000000 : ℝ)|=(2253315049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s9_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2210193039/10000000000 : ℝ)*x 0 + (2632279833/5000000000 : ℝ)*x 1 + (337139511/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2210193039/10000000000 : ℝ)^4123 ≤ (13421801872943/100000000000000 : ℝ)^3099 := by
    have hnat : (2210193039 : ℕ)^4123*100000000000000^3099 ≤ 13421801872943^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210193039 10000000000 13421801872943 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632279833/5000000000 : ℝ)^4123 ≤ (21294230482563/50000000000000 : ℝ)^3099 := by
    have hnat : (2632279833 : ℕ)^4123*50000000000000^3099 ≤ 21294230482563^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632279833 5000000000 21294230482563 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337139511/625000000 : ℝ)^4123 ≤ (43989737142909/100000000000000 : ℝ)^3099 := by
    have hnat : (337139511 : ℕ)^4123*100000000000000^3099 ≤ 43989737142909^3099*625000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337139511 625000000 43989737142909 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2210193039/10000000000 : ℝ), (2632279833/5000000000 : ℝ), (337139511/625000000 : ℝ)] ![(13421801872943/100000000000000 : ℝ), (21294230482563/50000000000000 : ℝ), (43989737142909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2210193039/10000000000 : ℝ)|^4123 ≤ (13421801872943/100000000000000 : ℝ)^3099
        have hw : |(-2210193039/10000000000 : ℝ)|=(2210193039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632279833/5000000000 : ℝ)|^4123 ≤ (21294230482563/50000000000000 : ℝ)^3099
        have hw : |(2632279833/5000000000 : ℝ)|=(2632279833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337139511/625000000 : ℝ)|^4123 ≤ (43989737142909/100000000000000 : ℝ)^3099
        have hw : |(337139511/625000000 : ℝ)|=(337139511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s9_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328052219/2500000000 : ℝ)*x 0 + (-2146315967/10000000000 : ℝ)*x 1 + (1348558047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328052219/2500000000 : ℝ)^4123 ≤ (43102060933279/100000000000000 : ℝ)^3099 := by
    have hnat : (1328052219 : ℕ)^4123*100000000000000^3099 ≤ 43102060933279^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328052219 2500000000 43102060933279 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2146315967/10000000000 : ℝ)^4123 ≤ (12908201776509/100000000000000 : ℝ)^3099 := by
    have hnat : (2146315967 : ℕ)^4123*100000000000000^3099 ≤ 12908201776509^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146315967 10000000000 12908201776509 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348558047/2500000000 : ℝ)^4123 ≤ (2749358579569/6250000000000 : ℝ)^3099 := by
    have hnat : (1348558047 : ℕ)^4123*6250000000000^3099 ≤ 2749358579569^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348558047 2500000000 2749358579569 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328052219/2500000000 : ℝ), (-2146315967/10000000000 : ℝ), (1348558047/2500000000 : ℝ)] ![(43102060933279/100000000000000 : ℝ), (12908201776509/100000000000000 : ℝ), (2749358579569/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328052219/2500000000 : ℝ)|^4123 ≤ (43102060933279/100000000000000 : ℝ)^3099
        have hw : |(1328052219/2500000000 : ℝ)|=(1328052219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2146315967/10000000000 : ℝ)|^4123 ≤ (12908201776509/100000000000000 : ℝ)^3099
        have hw : |(-2146315967/10000000000 : ℝ)|=(2146315967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348558047/2500000000 : ℝ)|^4123 ≤ (2749358579569/6250000000000 : ℝ)^3099
        have hw : |(1348558047/2500000000 : ℝ)|=(1348558047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s9_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312209013/10000000000 : ℝ)*x 0 + (5394231829/10000000000 : ℝ)*x 1 + (-214631627/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312209013/10000000000 : ℝ)^4123 ≤ (21551031206083/50000000000000 : ℝ)^3099 := by
    have hnat : (5312209013 : ℕ)^4123*50000000000000^3099 ≤ 21551031206083^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312209013 10000000000 21551031206083 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394231829/10000000000 : ℝ)^4123 ≤ (439897333781/1000000000000 : ℝ)^3099 := by
    have hnat : (5394231829 : ℕ)^4123*1000000000000^3099 ≤ 439897333781^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394231829 10000000000 439897333781 1000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214631627/1000000000 : ℝ)^4123 ≤ (12908204200921/100000000000000 : ℝ)^3099 := by
    have hnat : (214631627 : ℕ)^4123*100000000000000^3099 ≤ 12908204200921^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214631627 1000000000 12908204200921 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312209013/10000000000 : ℝ), (5394231829/10000000000 : ℝ), (-214631627/1000000000 : ℝ)] ![(21551031206083/50000000000000 : ℝ), (439897333781/1000000000000 : ℝ), (12908204200921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312209013/10000000000 : ℝ)|^4123 ≤ (21551031206083/50000000000000 : ℝ)^3099
        have hw : |(5312209013/10000000000 : ℝ)|=(5312209013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394231829/10000000000 : ℝ)|^4123 ≤ (439897333781/1000000000000 : ℝ)^3099
        have hw : |(5394231829/10000000000 : ℝ)|=(5394231829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214631627/1000000000 : ℝ)|^4123 ≤ (12908204200921/100000000000000 : ℝ)^3099
        have hw : |(-214631627/1000000000 : ℝ)|=(214631627/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_s9_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (547172041/1250000000 : ℝ)*x 0 + (2252996357/5000000000 : ℝ)*x 1 + (1063127293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547172041/1250000000 : ℝ)^4123 ≤ (6663317113401/20000000000000 : ℝ)^3099 := by
    have hnat : (547172041 : ℕ)^4123*20000000000000^3099 ≤ 6663317113401^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547172041 1250000000 6663317113401 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252996357/5000000000 : ℝ)^4123 ≤ (8656309400821/25000000000000 : ℝ)^3099 := by
    have hnat : (2252996357 : ℕ)^4123*25000000000000^3099 ≤ 8656309400821^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252996357 5000000000 8656309400821 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1063127293/2500000000 : ℝ)^4123 ≤ (32058176813897/100000000000000 : ℝ)^3099 := by
    have hnat : (1063127293 : ℕ)^4123*100000000000000^3099 ≤ 32058176813897^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1063127293 2500000000 32058176813897 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547172041/1250000000 : ℝ), (2252996357/5000000000 : ℝ), (1063127293/2500000000 : ℝ)] ![(6663317113401/20000000000000 : ℝ), (8656309400821/25000000000000 : ℝ), (32058176813897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547172041/1250000000 : ℝ)|^4123 ≤ (6663317113401/20000000000000 : ℝ)^3099
        have hw : |(547172041/1250000000 : ℝ)|=(547172041/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252996357/5000000000 : ℝ)|^4123 ≤ (8656309400821/25000000000000 : ℝ)^3099
        have hw : |(2252996357/5000000000 : ℝ)|=(2252996357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1063127293/2500000000 : ℝ)|^4123 ≤ (32058176813897/100000000000000 : ℝ)^3099
        have hw : |(1063127293/2500000000 : ℝ)|=(1063127293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5617/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6997/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11233/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2799/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11233/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2799/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11233/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11233/100000 : ℝ) ^ (8245/2048 : ℝ) ≤ (7522824125010967/50000000000000000000 : ℝ) := by
    have hpowers : (11233/100000 : ℝ)^8245 ≤ (7522824125010967/50000000000000000000 : ℝ)^2048 := by
      have hnat : (11233 : ℕ)^8245*50000000000000000000^2048 ≤ 7522824125010967^2048*100000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11233 100000 7522824125010967 50000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11233/100000 : ℝ)) (X := (7522824125010967/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2799/20000 : ℝ) ^ (8245/2048 : ℝ) ≤ (36457788740081121/100000000000000000000 : ℝ) := by
    have hpowers : (2799/20000 : ℝ)^8245 ≤ (36457788740081121/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2799 : ℕ)^8245*100000000000000000000^2048 ≤ 36457788740081121^2048*20000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2799 20000 36457788740081121 100000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2799/20000 : ℝ)) (X := (36457788740081121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007522824125010967/25000000000000000000 : ℝ) ≤ (5000373681063809/5000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (25007522824125010967/25000000000000000000 : ℝ)^2048 ≤ (5000373681063809/5000000000000000 : ℝ)^8245 := by
      have hnat : (25007522824125010967 : ℕ)^2048*5000000000000000^8245 ≤ 5000373681063809^8245*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007522824125010967 25000000000000000000 5000373681063809 5000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000373681063809/5000000000000000 : ℝ)) (X := (25007522824125010967/25000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010300687398020611/20000000000000000000 : ℝ) ≤ (10001279061606339/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (20010300687398020611/20000000000000000000 : ℝ)^2048 ≤ (10001279061606339/10000000000000000 : ℝ)^8245 := by
      have hnat : (20010300687398020611 : ℕ)^2048*10000000000000000^8245 ≤ 10001279061606339^8245*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010300687398020611 20000000000000000000 10001279061606339 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001279061606339/10000000000000000 : ℝ)) (X := (20010300687398020611/20000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036457788740081121/50000000000000000000 : ℝ) ≤ (500090538054253/500000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (50036457788740081121/50000000000000000000 : ℝ)^2048 ≤ (500090538054253/500000000000000 : ℝ)^8245 := by
      have hnat : (50036457788740081121 : ℕ)^2048*500000000000000^8245 ≤ 500090538054253^8245*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036457788740081121 50000000000000000000 500090538054253 500000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500090538054253/500000000000000 : ℝ)) (X := (50036457788740081121/50000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7522824125010967/50000000000000000000 : ℝ) ≤ ((2761011905370753493/2762000000000000000 : ℝ)+2*(531699478721/276200000000000 : ℝ)*(11233/100000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (2761011905370753493/2762000000000000000 : ℝ)+2*(531699478721/276200000000000 : ℝ)*(11233/100000 : ℝ)=(5000373681063809/5000000000000000 : ℝ) by norm_num, show 1+2*(7522824125010967/50000000000000000000 : ℝ)=(25007522824125010967/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36457788740081121/100000000000000000000 : ℝ)+(7522824125010967/50000000000000000000 : ℝ) ≤ ((2761011905370753493/2762000000000000000 : ℝ)+(531699478721/276200000000000 : ℝ)*((2799/20000 : ℝ)+(11233/100000 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (2761011905370753493/2762000000000000000 : ℝ)+(531699478721/276200000000000 : ℝ)*((2799/20000 : ℝ)+(11233/100000 : ℝ))=(10001279061606339/10000000000000000 : ℝ) by norm_num, show 1+(36457788740081121/100000000000000000000 : ℝ)+(7522824125010967/50000000000000000000 : ℝ)=(20010300687398020611/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36457788740081121/100000000000000000000 : ℝ) ≤ ((2761011905370753493/2762000000000000000 : ℝ)+2*(531699478721/276200000000000 : ℝ)*(2799/20000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (2761011905370753493/2762000000000000000 : ℝ)+2*(531699478721/276200000000000 : ℝ)*(2799/20000 : ℝ)=(500090538054253/500000000000000 : ℝ) by norm_num, show 1+2*(36457788740081121/100000000000000000000 : ℝ)=(50036457788740081121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2761011905370753493/2762000000000000000 : ℝ)*(X 1 0+X 2 0)+(531699478721/276200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (2761011905370753493/2762000000000000000 : ℝ)) (alpha := (531699478721/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2761011905370753493/2762000000000000000 : ℝ)*(X 0 1+X 2 1)+(531699478721/276200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (2761011905370753493/2762000000000000000 : ℝ)) (alpha := (531699478721/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2761011905370753493/2762000000000000000 : ℝ)*(X 0 2+X 1 2)+(531699478721/276200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (11233/100000 : ℝ)) (hi := (2799/20000 : ℝ)) (c := (2761011905370753493/2762000000000000000 : ℝ)) (alpha := (531699478721/276200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2210188049/10000000000 : ℝ)*X 0 0+(5394559443/10000000000 : ℝ)*X 0 1+(5264233497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334062569/625000000 : ℝ)*X 1 0+(-569078653/2500000000 : ℝ)*X 1 1+(526423379/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534500159/1000000000 : ℝ)*X 2 0+(1316058361/2500000000 : ℝ)*X 2 1+(-2276314423/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4377366399/10000000000 : ℝ)*X 0 0+(4251869469/10000000000 : ℝ)*X 0 1+(2253315049/5000000000 : ℝ)*X 0 2+(4377366399/10000000000 : ℝ)*X 1 0+(4251869469/10000000000 : ℝ)*X 1 1+(2253315049/5000000000 : ℝ)*X 1 2+(4377366399/10000000000 : ℝ)*X 2 0+(4251869469/10000000000 : ℝ)*X 2 1+(2253315049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2210193039/10000000000 : ℝ)*X 0 0+(2632279833/5000000000 : ℝ)*X 0 1+(337139511/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328052219/2500000000 : ℝ)*X 1 0+(-2146315967/10000000000 : ℝ)*X 1 1+(1348558047/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s9_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312209013/10000000000 : ℝ)*X 2 0+(5394231829/10000000000 : ℝ)*X 2 1+(-214631627/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s9_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547172041/1250000000 : ℝ)*X 0 0+(2252996357/5000000000 : ℝ)*X 0 1+(1063127293/2500000000 : ℝ)*X 0 2+(547172041/1250000000 : ℝ)*X 1 0+(2252996357/5000000000 : ℝ)*X 1 1+(1063127293/2500000000 : ℝ)*X 1 2+(547172041/1250000000 : ℝ)*X 2 0+(2252996357/5000000000 : ℝ)*X 2 1+(1063127293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_s9_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (182331169094573213993531097/34525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (422378123/100000000000000 : ℝ)*(base19) + (52514411/5000000000000 : ℝ)*(base23) + (12944383/25000000000000 : ℝ)*(lower2) + (61282119/25000000000000 : ℝ)*(upper5) + (2899596665829543/50000000000000 : ℝ)*(major0) + (2899596665829543/50000000000000 : ℝ)*(major1) + (2899596665829543/50000000000000 : ℝ)*(major2) + (1918271331519/25000000000 : ℝ)*(sp0) + (7673117584858227/100000000000000 : ℝ)*(sp1) + (7673121373192751/100000000000000 : ℝ)*(sp2) + (61332171186711/1562500000000 : ℝ)*(sp3) + (9274351243/25000000000000 : ℝ)*(sp4) + (2208122311/50000000000000 : ℝ)*(sp5) + (5107849869/100000000000000 : ℝ)*(sp7) + (981316015949843/25000000000000 : ℝ)*(f.failure) + (1918280605870243/25000000000000 : ℝ)*(f.sum) + (38183034079597/6905000000000000000000000000 : ℝ)*base66 + (3288858635936526301/138100000000000000000000000000000 : ℝ)*base68 + (846304062354326301/138100000000000000000000000000000 : ℝ)*base70 + (1036377124009926301/138100000000000000000000000000000 : ℝ)*base72 + (47114321686317/6905000000000000000000000000 : ℝ)*base74 + (594220768345726301/138100000000000000000000000000000 : ℝ)*base76 + (1160297928850926301/138100000000000000000000000000000 : ℝ)*base78 + (14792061658273699/138100000000000000000000000000000 : ℝ)*base79 + (4731280011683/1726250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11662813/2500000000000000000000 : ℝ)*base90 + (11662813/2500000000000000000000 : ℝ)*base92 + (11662813/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (304686620831178508963746591/69050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211454289/100000000000000 : ℝ)*(base19) + (132028599/25000000000000 : ℝ)*(base23) + (2469109/100000000000000 : ℝ)*(upper3) + (22862417/20000000000000 : ℝ)*(lower4) + (119592721/100000000000000 : ℝ)*(upper5) + (5828390003663671/100000000000000 : ℝ)*(major0) + (5828390003663671/100000000000000 : ℝ)*(major1) + (5828390003663671/100000000000000 : ℝ)*(major2) + (7766505221/100000000000000 : ℝ)*(sp0) + (1578015401/10000000000000 : ℝ)*(sp1) + (1927936464858593/25000000000000 : ℝ)*(sp4) + (7711737634331293/100000000000000 : ℝ)*(sp5) + (1927938274456299/25000000000000 : ℝ)*(sp6) + (1972513117151361/50000000000000 : ℝ)*(sp7) + (1972513117151361/50000000000000 : ℝ)*(f.failure) + (963969203242449/12500000000000 : ℝ)*(f.sum) + (71648359810199/13810000000000000000000000000 : ℝ)*base66 + (494070875447762803/276200000000000000000000000000000 : ℝ)*base67 + (1496553046701762803/276200000000000000000000000000000 : ℝ)*base69 + (3646578486060437197/276200000000000000000000000000000 : ℝ)*base72 + (2254562877621/13810000000000000000000000000 : ℝ)*base73 + (5974883137266762803/276200000000000000000000000000000 : ℝ)*base75 + (454851248531562803/276200000000000000000000000000000 : ℝ)*base77 + (2294405496277962803/276200000000000000000000000000000 : ℝ)*base79 + (23749700728951/13810000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (8774449/5000000000000000000000 : ℝ)*base89 + (8774449/5000000000000000000000 : ℝ)*base91 + (8774449/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1053_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1053_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1053_box_0 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2080280607/10000000000 : ℝ)*x 0 + (5377540757/10000000000 : ℝ)*x 1 + (5377540493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2080280607/10000000000 : ℝ)^4123 ≤ (3095633378733/25000000000000 : ℝ)^3099 := by
    have hnat : (2080280607 : ℕ)^4123*25000000000000^3099 ≤ 3095633378733^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080280607 10000000000 3095633378733 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377540757/10000000000 : ℝ)^4123 ≤ (1752349386657/4000000000000 : ℝ)^3099 := by
    have hnat : (5377540757 : ℕ)^4123*4000000000000^3099 ≤ 1752349386657^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377540757 10000000000 1752349386657 4000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5377540493/10000000000 : ℝ)^4123 ≤ (5476091475633/12500000000000 : ℝ)^3099 := by
    have hnat : (5377540493 : ℕ)^4123*12500000000000^3099 ≤ 5476091475633^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377540493 10000000000 5476091475633 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2080280607/10000000000 : ℝ), (5377540757/10000000000 : ℝ), (5377540493/10000000000 : ℝ)] ![(3095633378733/25000000000000 : ℝ), (1752349386657/4000000000000 : ℝ), (5476091475633/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2080280607/10000000000 : ℝ)|^4123 ≤ (3095633378733/25000000000000 : ℝ)^3099
        have hw : |(-2080280607/10000000000 : ℝ)|=(2080280607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377540757/10000000000 : ℝ)|^4123 ≤ (1752349386657/4000000000000 : ℝ)^3099
        have hw : |(5377540757/10000000000 : ℝ)|=(5377540757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5377540493/10000000000 : ℝ)|^4123 ≤ (5476091475633/12500000000000 : ℝ)^3099
        have hw : |(5377540493/10000000000 : ℝ)|=(5377540493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_1 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295055449/10000000000 : ℝ)*x 0 + (-438381589/2000000000 : ℝ)*x 1 + (537754071/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295055449/10000000000 : ℝ)^4123 ≤ (21458495976753/50000000000000 : ℝ)^3099 := by
    have hnat : (5295055449 : ℕ)^4123*50000000000000^3099 ≤ 21458495976753^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295055449 10000000000 21458495976753 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438381589/2000000000 : ℝ)^4123 ≤ (530970954883/4000000000000 : ℝ)^3099 := by
    have hnat : (438381589 : ℕ)^4123*4000000000000^3099 ≤ 530970954883^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438381589 2000000000 530970954883 4000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537754071/1000000000 : ℝ)^4123 ≤ (5476091769627/12500000000000 : ℝ)^3099 := by
    have hnat : (537754071 : ℕ)^4123*12500000000000^3099 ≤ 5476091769627^3099*1000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537754071 1000000000 5476091769627 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295055449/10000000000 : ℝ), (-438381589/2000000000 : ℝ), (537754071/1000000000 : ℝ)] ![(21458495976753/50000000000000 : ℝ), (530970954883/4000000000000 : ℝ), (5476091769627/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295055449/10000000000 : ℝ)|^4123 ≤ (21458495976753/50000000000000 : ℝ)^3099
        have hw : |(5295055449/10000000000 : ℝ)|=(5295055449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438381589/2000000000 : ℝ)|^4123 ≤ (530970954883/4000000000000 : ℝ)^3099
        have hw : |(-438381589/2000000000 : ℝ)|=(438381589/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537754071/1000000000 : ℝ)|^4123 ≤ (5476091769627/12500000000000 : ℝ)^3099
        have hw : |(537754071/1000000000 : ℝ)|=(537754071/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_2 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647527763/5000000000 : ℝ)*x 0 + (5377540513/10000000000 : ℝ)*x 1 + (-547977027/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647527763/5000000000 : ℝ)^4123 ≤ (42916992783817/100000000000000 : ℝ)^3099 := by
    have hnat : (2647527763 : ℕ)^4123*100000000000000^3099 ≤ 42916992783817^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647527763 5000000000 42916992783817 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5377540513/10000000000 : ℝ)^4123 ≤ (21904366010917/50000000000000 : ℝ)^3099 := by
    have hnat : (5377540513 : ℕ)^4123*50000000000000^3099 ≤ 21904366010917^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377540513 10000000000 21904366010917 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (547977027/2500000000 : ℝ)^4123 ≤ (13274275185387/100000000000000 : ℝ)^3099 := by
    have hnat : (547977027 : ℕ)^4123*100000000000000^3099 ≤ 13274275185387^3099*2500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547977027 2500000000 13274275185387 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647527763/5000000000 : ℝ), (5377540513/10000000000 : ℝ), (-547977027/2500000000 : ℝ)] ![(42916992783817/100000000000000 : ℝ), (21904366010917/50000000000000 : ℝ), (13274275185387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647527763/5000000000 : ℝ)|^4123 ≤ (42916992783817/100000000000000 : ℝ)^3099
        have hw : |(2647527763/5000000000 : ℝ)|=(2647527763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5377540513/10000000000 : ℝ)|^4123 ≤ (21904366010917/50000000000000 : ℝ)^3099
        have hw : |(5377540513/10000000000 : ℝ)|=(5377540513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-547977027/2500000000 : ℝ)|^4123 ≤ (13274275185387/100000000000000 : ℝ)^3099
        have hw : |(-547977027/2500000000 : ℝ)|=(547977027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_3 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4485898741/10000000000 : ℝ)*x 0 + (4325272393/10000000000 : ℝ)*x 1 + (4325272109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4485898741/10000000000 : ℝ)^4123 ≤ (34419961004287/100000000000000 : ℝ)^3099 := by
    have hnat : (4485898741 : ℕ)^4123*100000000000000^3099 ≤ 34419961004287^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485898741 10000000000 34419961004287 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4325272393/10000000000 : ℝ)^4123 ≤ (4098752615257/12500000000000 : ℝ)^3099 := by
    have hnat : (4325272393 : ℕ)^4123*12500000000000^3099 ≤ 4098752615257^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325272393 10000000000 4098752615257 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4325272109/10000000000 : ℝ)^4123 ≤ (262320144461/800000000000 : ℝ)^3099 := by
    have hnat : (4325272109 : ℕ)^4123*800000000000^3099 ≤ 262320144461^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325272109 10000000000 262320144461 800000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4485898741/10000000000 : ℝ), (4325272393/10000000000 : ℝ), (4325272109/10000000000 : ℝ)] ![(34419961004287/100000000000000 : ℝ), (4098752615257/12500000000000 : ℝ), (262320144461/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4485898741/10000000000 : ℝ)|^4123 ≤ (34419961004287/100000000000000 : ℝ)^3099
        have hw : |(4485898741/10000000000 : ℝ)|=(4485898741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4325272393/10000000000 : ℝ)|^4123 ≤ (4098752615257/12500000000000 : ℝ)^3099
        have hw : |(4325272393/10000000000 : ℝ)|=(4325272393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4325272109/10000000000 : ℝ)|^4123 ≤ (262320144461/800000000000 : ℝ)^3099
        have hw : |(4325272109/10000000000 : ℝ)|=(4325272109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_4 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-117074133/500000000 : ℝ)*x 0 + (2639947927/5000000000 : ℝ)*x 1 + (5279895787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (117074133/500000000 : ℝ)^4123 ≤ (7246401052479/50000000000000 : ℝ)^3099 := by
    have hnat : (117074133 : ℕ)^4123*50000000000000^3099 ≤ 7246401052479^3099*500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117074133 500000000 7246401052479 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2639947927/5000000000 : ℝ)^4123 ≤ (42753599303507/100000000000000 : ℝ)^3099 := by
    have hnat : (2639947927 : ℕ)^4123*100000000000000^3099 ≤ 42753599303507^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639947927 5000000000 42753599303507 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279895787/10000000000 : ℝ)^4123 ≤ (2672099911357/6250000000000 : ℝ)^3099 := by
    have hnat : (5279895787 : ℕ)^4123*6250000000000^3099 ≤ 2672099911357^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279895787 10000000000 2672099911357 6250000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-117074133/500000000 : ℝ), (2639947927/5000000000 : ℝ), (5279895787/10000000000 : ℝ)] ![(7246401052479/50000000000000 : ℝ), (42753599303507/100000000000000 : ℝ), (2672099911357/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-117074133/500000000 : ℝ)|^4123 ≤ (7246401052479/50000000000000 : ℝ)^3099
        have hw : |(-117074133/500000000 : ℝ)|=(117074133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2639947927/5000000000 : ℝ)|^4123 ≤ (42753599303507/100000000000000 : ℝ)^3099
        have hw : |(2639947927/5000000000 : ℝ)|=(2639947927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279895787/10000000000 : ℝ)|^4123 ≤ (2672099911357/6250000000000 : ℝ)^3099
        have hw : |(5279895787/10000000000 : ℝ)|=(5279895787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_5 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (670522647/1250000000 : ℝ)*x 0 + (-2230042139/10000000000 : ℝ)*x 1 + (5279895719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (670522647/1250000000 : ℝ)^4123 ≤ (4366399645409/10000000000000 : ℝ)^3099 := by
    have hnat : (670522647 : ℕ)^4123*10000000000000^3099 ≤ 4366399645409^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      670522647 1250000000 4366399645409 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2230042139/10000000000 : ℝ)^4123 ≤ (212225088627/1562500000000 : ℝ)^3099 := by
    have hnat : (2230042139 : ℕ)^4123*1562500000000^3099 ≤ 212225088627^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230042139 10000000000 212225088627 1562500000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279895719/10000000000 : ℝ)^4123 ≤ (5344199731143/12500000000000 : ℝ)^3099 := by
    have hnat : (5279895719 : ℕ)^4123*12500000000000^3099 ≤ 5344199731143^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279895719 10000000000 5344199731143 12500000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(670522647/1250000000 : ℝ), (-2230042139/10000000000 : ℝ), (5279895719/10000000000 : ℝ)] ![(4366399645409/10000000000000 : ℝ), (212225088627/1562500000000 : ℝ), (5344199731143/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(670522647/1250000000 : ℝ)|^4123 ≤ (4366399645409/10000000000000 : ℝ)^3099
        have hw : |(670522647/1250000000 : ℝ)|=(670522647/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2230042139/10000000000 : ℝ)|^4123 ≤ (212225088627/1562500000000 : ℝ)^3099
        have hw : |(-2230042139/10000000000 : ℝ)|=(2230042139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279895719/10000000000 : ℝ)|^4123 ≤ (5344199731143/12500000000000 : ℝ)^3099
        have hw : |(5279895719/10000000000 : ℝ)|=(5279895719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_6 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682090431/5000000000 : ℝ)*x 0 + (1055979203/2000000000 : ℝ)*x 1 + (-2230042167/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682090431/5000000000 : ℝ)^4123 ≤ (54579991317/125000000000 : ℝ)^3099 := by
    have hnat : (2682090431 : ℕ)^4123*125000000000^3099 ≤ 54579991317^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682090431 5000000000 54579991317 125000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1055979203/2000000000 : ℝ)^4123 ≤ (4275360103797/10000000000000 : ℝ)^3099 := by
    have hnat : (1055979203 : ℕ)^4123*10000000000000^3099 ≤ 4275360103797^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055979203 2000000000 4275360103797 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230042167/10000000000 : ℝ)^4123 ≤ (13582405899017/100000000000000 : ℝ)^3099 := by
    have hnat : (2230042167 : ℕ)^4123*100000000000000^3099 ≤ 13582405899017^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230042167 10000000000 13582405899017 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682090431/5000000000 : ℝ), (1055979203/2000000000 : ℝ), (-2230042167/10000000000 : ℝ)] ![(54579991317/125000000000 : ℝ), (4275360103797/10000000000000 : ℝ), (13582405899017/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682090431/5000000000 : ℝ)|^4123 ≤ (54579991317/125000000000 : ℝ)^3099
        have hw : |(2682090431/5000000000 : ℝ)|=(2682090431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1055979203/2000000000 : ℝ)|^4123 ≤ (4275360103797/10000000000000 : ℝ)^3099
        have hw : |(1055979203/2000000000 : ℝ)|=(1055979203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230042167/10000000000 : ℝ)|^4123 ≤ (13582405899017/100000000000000 : ℝ)^3099
        have hw : |(-2230042167/10000000000 : ℝ)|=(2230042167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_7 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (853702171/2000000000 : ℝ)*x 0 + (4433944747/10000000000 : ℝ)*x 1 + (2216972251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853702171/2000000000 : ℝ)^4123 ≤ (16109383807631/50000000000000 : ℝ)^3099 := by
    have hnat : (853702171 : ℕ)^4123*50000000000000^3099 ≤ 16109383807631^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853702171 2000000000 16109383807631 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4433944747/10000000000 : ℝ)^4123 ≤ (33890617430231/100000000000000 : ℝ)^3099 := by
    have hnat : (4433944747 : ℕ)^4123*100000000000000^3099 ≤ 33890617430231^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4433944747 10000000000 33890617430231 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2216972251/5000000000 : ℝ)^4123 ≤ (3389061493881/10000000000000 : ℝ)^3099 := by
    have hnat : (2216972251 : ℕ)^4123*10000000000000^3099 ≤ 3389061493881^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2216972251 5000000000 3389061493881 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853702171/2000000000 : ℝ), (4433944747/10000000000 : ℝ), (2216972251/5000000000 : ℝ)] ![(16109383807631/50000000000000 : ℝ), (33890617430231/100000000000000 : ℝ), (3389061493881/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853702171/2000000000 : ℝ)|^4123 ≤ (16109383807631/50000000000000 : ℝ)^3099
        have hw : |(853702171/2000000000 : ℝ)|=(853702171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4433944747/10000000000 : ℝ)|^4123 ≤ (33890617430231/100000000000000 : ℝ)^3099
        have hw : |(4433944747/10000000000 : ℝ)|=(4433944747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2216972251/5000000000 : ℝ)|^4123 ≤ (3389061493881/10000000000000 : ℝ)^3099
        have hw : |(2216972251/5000000000 : ℝ)|=(2216972251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_8 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1143485457/5000000000 : ℝ)*x 0 + (5213663693/10000000000 : ℝ)*x 1 + (1077427813/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1143485457/5000000000 : ℝ)^4123 ≤ (2809128862439/20000000000000 : ℝ)^3099 := by
    have hnat : (1143485457 : ℕ)^4123*20000000000000^3099 ≤ 2809128862439^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143485457 5000000000 2809128862439 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213663693/10000000000 : ℝ)^4123 ≤ (21020779589177/50000000000000 : ℝ)^3099 := by
    have hnat : (5213663693 : ℕ)^4123*50000000000000^3099 ≤ 21020779589177^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213663693 10000000000 21020779589177 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077427813/2000000000 : ℝ)^4123 ≤ (21956398245749/50000000000000 : ℝ)^3099 := by
    have hnat : (1077427813 : ℕ)^4123*50000000000000^3099 ≤ 21956398245749^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077427813 2000000000 21956398245749 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1143485457/5000000000 : ℝ), (5213663693/10000000000 : ℝ), (1077427813/2000000000 : ℝ)] ![(2809128862439/20000000000000 : ℝ), (21020779589177/50000000000000 : ℝ), (21956398245749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1143485457/5000000000 : ℝ)|^4123 ≤ (2809128862439/20000000000000 : ℝ)^3099
        have hw : |(-1143485457/5000000000 : ℝ)|=(1143485457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213663693/10000000000 : ℝ)|^4123 ≤ (21020779589177/50000000000000 : ℝ)^3099
        have hw : |(5213663693/10000000000 : ℝ)|=(5213663693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077427813/2000000000 : ℝ)|^4123 ≤ (21956398245749/50000000000000 : ℝ)^3099
        have hw : |(1077427813/2000000000 : ℝ)|=(1077427813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_9 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644128319/5000000000 : ℝ)*x 0 + (-2188088639/10000000000 : ℝ)*x 1 + (5387139001/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644128319/5000000000 : ℝ)^4123 ≤ (1713747763543/4000000000000 : ℝ)^3099 := by
    have hnat : (2644128319 : ℕ)^4123*4000000000000^3099 ≤ 1713747763543^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644128319 5000000000 1713747763543 4000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188088639/10000000000 : ℝ)^4123 ≤ (6621755049987/50000000000000 : ℝ)^3099 := by
    have hnat : (2188088639 : ℕ)^4123*50000000000000^3099 ≤ 6621755049987^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188088639 10000000000 6621755049987 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5387139001/10000000000 : ℝ)^4123 ≤ (21956397898713/50000000000000 : ℝ)^3099 := by
    have hnat : (5387139001 : ℕ)^4123*50000000000000^3099 ≤ 21956397898713^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387139001 10000000000 21956397898713 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644128319/5000000000 : ℝ), (-2188088639/10000000000 : ℝ), (5387139001/10000000000 : ℝ)] ![(1713747763543/4000000000000 : ℝ), (6621755049987/50000000000000 : ℝ), (21956397898713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644128319/5000000000 : ℝ)|^4123 ≤ (1713747763543/4000000000000 : ℝ)^3099
        have hw : |(2644128319/5000000000 : ℝ)|=(2644128319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2188088639/10000000000 : ℝ)|^4123 ≤ (6621755049987/50000000000000 : ℝ)^3099
        have hw : |(-2188088639/10000000000 : ℝ)|=(2188088639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5387139001/10000000000 : ℝ)|^4123 ≤ (21956397898713/50000000000000 : ℝ)^3099
        have hw : |(5387139001/10000000000 : ℝ)|=(5387139001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_10 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288256713/10000000000 : ℝ)*x 0 + (269356951/500000000 : ℝ)*x 1 + (-34188883/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288256713/10000000000 : ℝ)^4123 ≤ (42843694896977/100000000000000 : ℝ)^3099 := by
    have hnat : (5288256713 : ℕ)^4123*100000000000000^3099 ≤ 42843694896977^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288256713 10000000000 42843694896977 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269356951/500000000 : ℝ)^4123 ≤ (43912796003479/100000000000000 : ℝ)^3099 := by
    have hnat : (269356951 : ℕ)^4123*100000000000000^3099 ≤ 43912796003479^3099*500000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269356951 500000000 43912796003479 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (34188883/156250000 : ℝ)^4123 ≤ (3310877269327/25000000000000 : ℝ)^3099 := by
    have hnat : (34188883 : ℕ)^4123*25000000000000^3099 ≤ 3310877269327^3099*156250000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34188883 156250000 3310877269327 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288256713/10000000000 : ℝ), (269356951/500000000 : ℝ), (-34188883/156250000 : ℝ)] ![(42843694896977/100000000000000 : ℝ), (43912796003479/100000000000000 : ℝ), (3310877269327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288256713/10000000000 : ℝ)|^4123 ≤ (42843694896977/100000000000000 : ℝ)^3099
        have hw : |(5288256713/10000000000 : ℝ)|=(5288256713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269356951/500000000 : ℝ)|^4123 ≤ (43912796003479/100000000000000 : ℝ)^3099
        have hw : |(269356951/500000000 : ℝ)|=(269356951/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-34188883/156250000 : ℝ)|^4123 ≤ (3310877269327/25000000000000 : ℝ)^3099
        have hw : |(-34188883/156250000 : ℝ)|=(34188883/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_11 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2253497287/5000000000 : ℝ)*x 0 + (4314583769/10000000000 : ℝ)*x 1 + (2157291941/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2253497287/5000000000 : ℝ)^4123 ≤ (6927096072791/20000000000000 : ℝ)^3099 := by
    have hnat : (2253497287 : ℕ)^4123*20000000000000^3099 ≤ 6927096072791^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253497287 5000000000 6927096072791 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4314583769/10000000000 : ℝ)^4123 ≤ (3268225924497/10000000000000 : ℝ)^3099 := by
    have hnat : (4314583769 : ℕ)^4123*10000000000000^3099 ≤ 3268225924497^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4314583769 10000000000 3268225924497 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2157291941/5000000000 : ℝ)^4123 ≤ (32682260383759/100000000000000 : ℝ)^3099 := by
    have hnat : (2157291941 : ℕ)^4123*100000000000000^3099 ≤ 32682260383759^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157291941 5000000000 32682260383759 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2253497287/5000000000 : ℝ), (4314583769/10000000000 : ℝ), (2157291941/5000000000 : ℝ)] ![(6927096072791/20000000000000 : ℝ), (3268225924497/10000000000000 : ℝ), (32682260383759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2253497287/5000000000 : ℝ)|^4123 ≤ (6927096072791/20000000000000 : ℝ)^3099
        have hw : |(2253497287/5000000000 : ℝ)|=(2253497287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4314583769/10000000000 : ℝ)|^4123 ≤ (3268225924497/10000000000000 : ℝ)^3099
        have hw : |(4314583769/10000000000 : ℝ)|=(4314583769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2157291941/5000000000 : ℝ)|^4123 ≤ (32682260383759/100000000000000 : ℝ)^3099
        have hw : |(2157291941/5000000000 : ℝ)|=(2157291941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_12 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067584741/5000000000 : ℝ)*x 0 + (2721213461/5000000000 : ℝ)*x 1 + (65898781/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067584741/5000000000 : ℝ)^4123 ≤ (3204772835509/25000000000000 : ℝ)^3099 := by
    have hnat : (1067584741 : ℕ)^4123*25000000000000^3099 ≤ 3204772835509^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067584741 5000000000 3204772835509 25000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721213461/5000000000 : ℝ)^4123 ≤ (22256700444157/50000000000000 : ℝ)^3099 := by
    have hnat : (2721213461 : ℕ)^4123*50000000000000^3099 ≤ 22256700444157^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721213461 5000000000 22256700444157 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65898781/125000000 : ℝ)^4123 ≤ (21333753875331/50000000000000 : ℝ)^3099 := by
    have hnat : (65898781 : ℕ)^4123*50000000000000^3099 ≤ 21333753875331^3099*125000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65898781 125000000 21333753875331 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067584741/5000000000 : ℝ), (2721213461/5000000000 : ℝ), (65898781/125000000 : ℝ)] ![(3204772835509/25000000000000 : ℝ), (22256700444157/50000000000000 : ℝ), (21333753875331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067584741/5000000000 : ℝ)|^4123 ≤ (3204772835509/25000000000000 : ℝ)^3099
        have hw : |(-1067584741/5000000000 : ℝ)|=(1067584741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721213461/5000000000 : ℝ)|^4123 ≤ (22256700444157/50000000000000 : ℝ)^3099
        have hw : |(2721213461/5000000000 : ℝ)|=(2721213461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65898781/125000000 : ℝ)|^4123 ≤ (21333753875331/50000000000000 : ℝ)^3099
        have hw : |(65898781/125000000 : ℝ)|=(65898781/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_13 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684918769/5000000000 : ℝ)*x 0 + (-2233105117/10000000000 : ℝ)*x 1 + (1054380457/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684918769/5000000000 : ℝ)^4123 ≤ (43725263174803/100000000000000 : ℝ)^3099 := by
    have hnat : (2684918769 : ℕ)^4123*100000000000000^3099 ≤ 43725263174803^3099*5000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684918769 5000000000 43725263174803 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2233105117/10000000000 : ℝ)^4123 ≤ (13607231158983/100000000000000 : ℝ)^3099 := by
    have hnat : (2233105117 : ℕ)^4123*100000000000000^3099 ≤ 13607231158983^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2233105117 10000000000 13607231158983 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054380457/2000000000 : ℝ)^4123 ≤ (42667505650967/100000000000000 : ℝ)^3099 := by
    have hnat : (1054380457 : ℕ)^4123*100000000000000^3099 ≤ 42667505650967^3099*2000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054380457 2000000000 42667505650967 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684918769/5000000000 : ℝ), (-2233105117/10000000000 : ℝ), (1054380457/2000000000 : ℝ)] ![(43725263174803/100000000000000 : ℝ), (13607231158983/100000000000000 : ℝ), (42667505650967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684918769/5000000000 : ℝ)|^4123 ≤ (43725263174803/100000000000000 : ℝ)^3099
        have hw : |(2684918769/5000000000 : ℝ)|=(2684918769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2233105117/10000000000 : ℝ)|^4123 ≤ (13607231158983/100000000000000 : ℝ)^3099
        have hw : |(-2233105117/10000000000 : ℝ)|=(2233105117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054380457/2000000000 : ℝ)|^4123 ≤ (42667505650967/100000000000000 : ℝ)^3099
        have hw : |(1054380457/2000000000 : ℝ)|=(1054380457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_14 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369837573/10000000000 : ℝ)*x 0 + (5271902133/10000000000 : ℝ)*x 1 + (-279138159/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369837573/10000000000 : ℝ)^4123 ≤ (4372526355397/10000000000000 : ℝ)^3099 := by
    have hnat : (5369837573 : ℕ)^4123*10000000000000^3099 ≤ 4372526355397^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369837573 10000000000 4372526355397 10000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271902133/10000000000 : ℝ)^4123 ≤ (42667504014281/100000000000000 : ℝ)^3099 := by
    have hnat : (5271902133 : ℕ)^4123*100000000000000^3099 ≤ 42667504014281^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271902133 10000000000 42667504014281 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279138159/1250000000 : ℝ)^4123 ≤ (6803616207773/50000000000000 : ℝ)^3099 := by
    have hnat : (279138159 : ℕ)^4123*50000000000000^3099 ≤ 6803616207773^3099*1250000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279138159 1250000000 6803616207773 50000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369837573/10000000000 : ℝ), (5271902133/10000000000 : ℝ), (-279138159/1250000000 : ℝ)] ![(4372526355397/10000000000000 : ℝ), (42667504014281/100000000000000 : ℝ), (6803616207773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369837573/10000000000 : ℝ)|^4123 ≤ (4372526355397/10000000000000 : ℝ)^3099
        have hw : |(5369837573/10000000000 : ℝ)|=(5369837573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271902133/10000000000 : ℝ)|^4123 ≤ (42667504014281/100000000000000 : ℝ)^3099
        have hw : |(5271902133/10000000000 : ℝ)|=(5271902133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279138159/1250000000 : ℝ)|^4123 ≤ (6803616207773/50000000000000 : ℝ)^3099
        have hw : |(-279138159/1250000000 : ℝ)|=(279138159/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1053_box_15 (p : ℝ) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250484799/10000000000 : ℝ)*x 0 + (4442835987/10000000000 : ℝ)*x 1 + (4442835927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250484799/10000000000 : ℝ)^4123 ≤ (32037874679711/100000000000000 : ℝ)^3099 := by
    have hnat : (4250484799 : ℕ)^4123*100000000000000^3099 ≤ 32037874679711^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250484799 10000000000 32037874679711 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4442835987/10000000000 : ℝ)^4123 ≤ (6796212591263/20000000000000 : ℝ)^3099 := by
    have hnat : (4442835987 : ℕ)^4123*20000000000000^3099 ≤ 6796212591263^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442835987 10000000000 6796212591263 20000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4442835927/10000000000 : ℝ)^4123 ≤ (33981062345767/100000000000000 : ℝ)^3099 := by
    have hnat : (4442835927 : ℕ)^4123*100000000000000^3099 ≤ 33981062345767^3099*10000000000^4123 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442835927 10000000000 33981062345767 100000000000000 4123 3099 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4123/1024 : ℝ)) 4123 3099 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250484799/10000000000 : ℝ), (4442835987/10000000000 : ℝ), (4442835927/10000000000 : ℝ)] ![(32037874679711/100000000000000 : ℝ), (6796212591263/20000000000000 : ℝ), (33981062345767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250484799/10000000000 : ℝ)|^4123 ≤ (32037874679711/100000000000000 : ℝ)^3099
        have hw : |(4250484799/10000000000 : ℝ)|=(4250484799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4442835987/10000000000 : ℝ)|^4123 ≤ (6796212591263/20000000000000 : ℝ)^3099
        have hw : |(4442835987/10000000000 : ℝ)|=(4442835987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4442835927/10000000000 : ℝ)|^4123 ≤ (33981062345767/100000000000000 : ℝ)^3099
        have hw : |(4442835927/10000000000 : ℝ)|=(4442835927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1053_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(3889/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59231/100000 : ℝ) ∧ (79531/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (82923/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6997/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5617/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6997/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5617/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6997/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5617/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5617/50000 : ℝ) ^ (8245/2048 : ℝ) ≤ (15051041298777247/100000000000000000000 : ℝ) := by
    have hpowers : (5617/50000 : ℝ)^8245 ≤ (15051041298777247/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5617 : ℕ)^8245*100000000000000000000^2048 ≤ 15051041298777247^2048*50000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5617 50000 15051041298777247 100000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5617/50000 : ℝ)) (X := (15051041298777247/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6997/50000 : ℝ) ^ (8245/2048 : ℝ) ≤ (18223651112582703/50000000000000000000 : ℝ) := by
    have hpowers : (6997/50000 : ℝ)^8245 ≤ (18223651112582703/50000000000000000000 : ℝ)^2048 := by
      have hnat : (6997 : ℕ)^8245*50000000000000000000^2048 ≤ 18223651112582703^2048*50000^8245 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6997 50000 18223651112582703 50000000000000000000 8245 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6997/50000 : ℝ)) (X := (18223651112582703/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50015051041298777247/50000000000000000000 : ℝ) ≤ (10000747629986103/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (50015051041298777247/50000000000000000000 : ℝ)^2048 ≤ (10000747629986103/10000000000000000 : ℝ)^8245 := by
      have hnat : (50015051041298777247 : ℕ)^2048*10000000000000000^8245 ≤ 10000747629986103^8245*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015051041298777247 50000000000000000000 10000747629986103 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000747629986103/10000000000000000 : ℝ)) (X := (50015051041298777247/50000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051498343523942653/100000000000000000000 : ℝ) ≤ (10001278935137173/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (100051498343523942653/100000000000000000000 : ℝ)^2048 ≤ (10001278935137173/10000000000000000 : ℝ)^8245 := by
      have hnat : (100051498343523942653 : ℕ)^2048*10000000000000000^8245 ≤ 10001278935137173^8245*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051498343523942653 100000000000000000000 10001278935137173 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001278935137173/10000000000000000 : ℝ)) (X := (100051498343523942653/100000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018223651112582703/25000000000000000000 : ℝ) ≤ (10001810240288243/10000000000000000 : ℝ) ^ (8245/2048 : ℝ) := by
    have hpowers : (25018223651112582703/25000000000000000000 : ℝ)^2048 ≤ (10001810240288243/10000000000000000 : ℝ)^8245 := by
      have hnat : (25018223651112582703 : ℕ)^2048*10000000000000000^8245 ≤ 10001810240288243^8245*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018223651112582703 25000000000000000000 10001810240288243 10000000000000000 2048 8245 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001810240288243/10000000000000000 : ℝ)) (X := (25018223651112582703/25000000000000000000 : ℝ)) (by norm_num) 8245 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(15051041298777247/100000000000000000000 : ℝ) ≤ ((21554786011427659/21562500000000000 : ℝ)+2*(53130515107/27600000000000 : ℝ)*(5617/50000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (21554786011427659/21562500000000000 : ℝ)+2*(53130515107/27600000000000 : ℝ)*(5617/50000 : ℝ)=(10000747629986103/10000000000000000 : ℝ) by norm_num, show 1+2*(15051041298777247/100000000000000000000 : ℝ)=(50015051041298777247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18223651112582703/50000000000000000000 : ℝ)+(15051041298777247/100000000000000000000 : ℝ) ≤ ((21554786011427659/21562500000000000 : ℝ)+(53130515107/27600000000000 : ℝ)*((6997/50000 : ℝ)+(5617/50000 : ℝ)))^(8245/2048 : ℝ) := by
    rw [show (21554786011427659/21562500000000000 : ℝ)+(53130515107/27600000000000 : ℝ)*((6997/50000 : ℝ)+(5617/50000 : ℝ))=(10001278935137173/10000000000000000 : ℝ) by norm_num, show 1+(18223651112582703/50000000000000000000 : ℝ)+(15051041298777247/100000000000000000000 : ℝ)=(100051498343523942653/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18223651112582703/50000000000000000000 : ℝ) ≤ ((21554786011427659/21562500000000000 : ℝ)+2*(53130515107/27600000000000 : ℝ)*(6997/50000 : ℝ))^(8245/2048 : ℝ) := by
    rw [show (21554786011427659/21562500000000000 : ℝ)+2*(53130515107/27600000000000 : ℝ)*(6997/50000 : ℝ)=(10001810240288243/10000000000000000 : ℝ) by norm_num, show 1+2*(18223651112582703/50000000000000000000 : ℝ)=(25018223651112582703/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21554786011427659/21562500000000000 : ℝ)*(X 1 0+X 2 0)+(53130515107/27600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (21554786011427659/21562500000000000 : ℝ)) (alpha := (53130515107/27600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21554786011427659/21562500000000000 : ℝ)*(X 0 1+X 2 1)+(53130515107/27600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (21554786011427659/21562500000000000 : ℝ)) (alpha := (53130515107/27600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21554786011427659/21562500000000000 : ℝ)*(X 0 2+X 1 2)+(53130515107/27600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8245/2048 : ℝ)) (lo := (5617/50000 : ℝ)) (hi := (6997/50000 : ℝ)) (c := (21554786011427659/21562500000000000 : ℝ)) (alpha := (53130515107/27600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2080280607/10000000000 : ℝ)*X 0 0+(5377540757/10000000000 : ℝ)*X 0 1+(5377540493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5295055449/10000000000 : ℝ)*X 1 0+(-438381589/2000000000 : ℝ)*X 1 1+(537754071/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2647527763/5000000000 : ℝ)*X 2 0+(5377540513/10000000000 : ℝ)*X 2 1+(-547977027/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4485898741/10000000000 : ℝ)*X 0 0+(4325272393/10000000000 : ℝ)*X 0 1+(4325272109/10000000000 : ℝ)*X 0 2+(4485898741/10000000000 : ℝ)*X 1 0+(4325272393/10000000000 : ℝ)*X 1 1+(4325272109/10000000000 : ℝ)*X 1 2+(4485898741/10000000000 : ℝ)*X 2 0+(4325272393/10000000000 : ℝ)*X 2 1+(4325272109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-117074133/500000000 : ℝ)*X 0 0+(2639947927/5000000000 : ℝ)*X 0 1+(5279895787/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((670522647/1250000000 : ℝ)*X 1 0+(-2230042139/10000000000 : ℝ)*X 1 1+(5279895719/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682090431/5000000000 : ℝ)*X 2 0+(1055979203/2000000000 : ℝ)*X 2 1+(-2230042167/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((853702171/2000000000 : ℝ)*X 0 0+(4433944747/10000000000 : ℝ)*X 0 1+(2216972251/5000000000 : ℝ)*X 0 2+(853702171/2000000000 : ℝ)*X 1 0+(4433944747/10000000000 : ℝ)*X 1 1+(2216972251/5000000000 : ℝ)*X 1 2+(853702171/2000000000 : ℝ)*X 2 0+(4433944747/10000000000 : ℝ)*X 2 1+(2216972251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1143485457/5000000000 : ℝ)*X 0 0+(5213663693/10000000000 : ℝ)*X 0 1+(1077427813/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2644128319/5000000000 : ℝ)*X 1 0+(-2188088639/10000000000 : ℝ)*X 1 1+(5387139001/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288256713/10000000000 : ℝ)*X 2 0+(269356951/500000000 : ℝ)*X 2 1+(-34188883/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2253497287/5000000000 : ℝ)*X 0 0+(4314583769/10000000000 : ℝ)*X 0 1+(2157291941/5000000000 : ℝ)*X 0 2+(2253497287/5000000000 : ℝ)*X 1 0+(4314583769/10000000000 : ℝ)*X 1 1+(2157291941/5000000000 : ℝ)*X 1 2+(2253497287/5000000000 : ℝ)*X 2 0+(4314583769/10000000000 : ℝ)*X 2 1+(2157291941/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1067584741/5000000000 : ℝ)*X 0 0+(2721213461/5000000000 : ℝ)*X 0 1+(65898781/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2684918769/5000000000 : ℝ)*X 1 0+(-2233105117/10000000000 : ℝ)*X 1 1+(1054380457/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369837573/10000000000 : ℝ)*X 2 0+(5271902133/10000000000 : ℝ)*X 2 1+(-279138159/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4250484799/10000000000 : ℝ)*X 0 0+(4442835987/10000000000 : ℝ)*X 0 1+(4442835927/10000000000 : ℝ)*X 0 2+(4250484799/10000000000 : ℝ)*X 1 0+(4442835987/10000000000 : ℝ)*X 1 1+(4442835927/10000000000 : ℝ)*X 1 2+(4250484799/10000000000 : ℝ)*X 2 0+(4442835987/10000000000 : ℝ)*X 2 1+(4442835927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1053_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3889/6250 : ℝ) ≤ (-71554551163269914887530897/115000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16386987/25000000000000 : ℝ)*(upper0) + (23872089/20000000000000 : ℝ)*(upper1) + (60096987/100000000000000 : ℝ)*(upper2) + (21154493/25000000000000 : ℝ)*(upper3) + (376289/6250000000000 : ℝ)*(upper5) + (961436721773871/25000000000000 : ℝ)*(major0) + (961436721773871/25000000000000 : ℝ)*(major1) + (961436721773871/25000000000000 : ℝ)*(major2) + (8557035373/100000000000000 : ℝ)*(sp3) + (5109187353133721/100000000000000 : ℝ)*(sp4) + (5109187353133721/100000000000000 : ℝ)*(sp5) + (159656562060583/3125000000000 : ℝ)*(sp6) + (3253797892043/125000000000 : ℝ)*(sp7) + (22170899383/12500000000000 : ℝ)*(sp14) + (1301523435334887/50000000000000 : ℝ)*(f.failure) + (5109187353133721/100000000000000 : ℝ)*(f.sum) + (112109688763/14375000000000000000000000 : ℝ)*base65 + (26824400087878723/718750000000000000000000000000 : ℝ)*base68 + (15432447347473/718750000000000000000000000000 : ℝ)*base70 + (3320933605308777/718750000000000000000000000000 : ℝ)*base71 + (1283716161849/115000000000000000000000000 : ℝ)*base73 + (7181478166527527/718750000000000000000000000000 : ℝ)*base75 + (3960976708308777/718750000000000000000000000000 : ℝ)*base77 + (5665862469566223/718750000000000000000000000000 : ℝ)*base80 + (1038006131439/28750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9628617/5000000000000000000000 : ℝ)*base90 + (9628617/5000000000000000000000 : ℝ)*base92 + (9628617/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (59231/100000 : ℝ) ≤ (212870997198485627623916331513/359375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16046359/25000000000000 : ℝ)*(upper3) + (4679561/50000000000000 : ℝ)*(upper4) + (39099023/50000000000000 : ℝ)*(lower5) + (30534693098003/781250000000 : ℝ)*(major0) + (30534693098003/781250000000 : ℝ)*(major1) + (30534693098003/781250000000 : ℝ)*(major2) + (2575825903841929/50000000000000 : ℝ)*(sp0) + (1287912560795127/25000000000000 : ℝ)*(sp1) + (5151654627743779/100000000000000 : ℝ)*(sp2) + (661370465850889/25000000000000 : ℝ)*(sp3) + (1144758063/25000000000000 : ℝ)*(sp5) + (194468981/100000000000000 : ℝ)*(sp6) + (47802639/25000000000000 : ℝ)*(sp7) + (1507264451/50000000000000 : ℝ)*(sp8) + (82671314206691/3125000000000 : ℝ)*(f.failure) + (128791370555319/2500000000000 : ℝ)*(f.sum) + (1150259751641/172500000000000000000000000 : ℝ)*base65 + (61728876477261/22460937500000000000000000000 : ℝ)*base67 + (418924338393419/89843750000000000000000000000 : ℝ)*base69 + (682922697612169/89843750000000000000000000000 : ℝ)*base71 + (83309170979/43125000000000000000000000 : ℝ)*base73 + (179230140657647/44921875000000000000000000000 : ℝ)*base75 + (135070838039761/22460937500000000000000000000 : ℝ)*base77 + (73383802635037/179687500000000000000000000000 : ℝ)*base80 + (472919741107/345000000000000000000000000 : ℝ)*base81 + (2461581/312500000000000000000 : ℝ)*base90 + (2461581/312500000000000000000 : ℝ)*base92 + (2461581/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (79531/100000 : ℝ) ≤ (57164904950155864264187879403/71875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (36062229/100000000000000 : ℝ)*(upper0) + (236151/400000000000 : ℝ)*(lower3) + (63851091/100000000000000 : ℝ)*(upper4) + (437673873288471/10000000000000 : ℝ)*(major0) + (437673873288471/10000000000000 : ℝ)*(major1) + (437673873288471/10000000000000 : ℝ)*(major2) + (635947163/2000000000000 : ℝ)*(sp1) + (248488593/400000000000 : ℝ)*(sp2) + (8072932289/25000000000000 : ℝ)*(sp3) + (780948189/100000000000000 : ℝ)*(sp4) + (5764509392774589/100000000000000 : ℝ)*(sp8) + (5764478376364629/100000000000000 : ℝ)*(sp9) + (22517375201463/390625000000 : ℝ)*(sp10) + (296242374005073/10000000000000 : ℝ)*(sp11) + (1481228015889943/50000000000000 : ℝ)*(f.failure) + (2882255086861389/50000000000000 : ℝ)*(f.sum) + (231148384581/46000000000000000000000000 : ℝ)*base66 + (112110539539773/287500000000000000000000000000 : ℝ)*base68 + (196821158452273/287500000000000000000000000000 : ℝ)*base70 + (1868290204052273/287500000000000000000000000000 : ℝ)*base72 + (2379912103937/46000000000000000000000000 : ℝ)*base73 + (613835049989773/287500000000000000000000000000 : ℝ)*base76 + (1440886743747727/287500000000000000000000000000 : ℝ)*base77 + (24411142307697727/287500000000000000000000000000 : ℝ)*base79 + (179968059511/46000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (181913/5000000000000000000000 : ℝ)*base90 + (181913/5000000000000000000000 : ℝ)*base92 + (181913/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-82923/100000 : ℝ) ≤ (-148997169342171206976332691351/179687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (17096269/10000000000000 : ℝ)*(upper3) + (20298901/50000000000000 : ℝ)*(lower4) + (11905327/12500000000000 : ℝ)*(upper5) + (4411224435491699/100000000000000 : ℝ)*(major0) + (4411224435491699/100000000000000 : ℝ)*(major1) + (4411224435491699/100000000000000 : ℝ)*(major2) + (1532657679/6250000000000 : ℝ)*(sp4) + (381460540597/100000000000000 : ℝ)*(sp5) + (489490642977/100000000000000 : ℝ)*(sp6) + (118290511227/50000000000000 : ℝ)*(sp7) + (2932133123701067/50000000000000 : ℝ)*(sp12) + (14659773273461/250000000000 : ℝ)*(sp13) + (5863801279282021/100000000000000 : ℝ)*(sp14) + (2985561574638541/100000000000000 : ℝ)*(sp15) + (1492899077830497/50000000000000 : ℝ)*(f.failure) + (5864290769924997/100000000000000 : ℝ)*(f.sum) + (5929618827413/1380000000000000000000000000 : ℝ)*base65 + (17858817872045437/2875000000000000000000000000000 : ℝ)*base68 + (16808279054795437/2875000000000000000000000000000 : ℝ)*base70 + (2209054924045437/2875000000000000000000000000000 : ℝ)*base72 + (7372589992433/1380000000000000000000000000 : ℝ)*base73 + (4712268425420437/2875000000000000000000000000000 : ℝ)*base76 + (14066911737170437/2875000000000000000000000000000 : ℝ)*base78 + (27555704248545437/2875000000000000000000000000000 : ℝ)*base80 + (2074697926073/1380000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (56646127/5000000000000000000000 : ℝ)*base90 + (56646127/5000000000000000000000 : ℝ)*base92 + (56646127/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1053_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6997/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5617/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59231/100000 : ℝ) else (79531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82923/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1053_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1053_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59231/100000 : ℝ) else (79531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82923/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1053_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1053_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8245/2048 : ℝ) ≤ p) (hpb : p ≤ (4123/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147740209/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2799/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11233/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3889/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(59231/100000 : ℝ) else (79531/100000 : ℝ) ≤ X j i ∧ X j i ≤ (82923/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1053_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
