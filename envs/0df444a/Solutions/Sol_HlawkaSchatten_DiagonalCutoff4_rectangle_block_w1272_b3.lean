-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1272_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:23.067042+00:00
-- url     : https://prove2.me/submissions/35e26ebe-c5e7-4d3e-bbce-56bc5d05b45c

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
theorem support_rectangle_w1272_box_0 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1983035367/10000000000 : ℝ)*x 0 + (5374370829/10000000000 : ℝ)*x 1 + (5374370193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1983035367/10000000000 : ℝ)^4233 ≤ (5916663091427/50000000000000 : ℝ)^3209 := by
    have hnat : (1983035367 : ℕ)^4233*50000000000000^3209 ≤ 5916663091427^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1983035367 10000000000 5916663091427 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5374370829/10000000000 : ℝ)^4233 ≤ (5510417542797/12500000000000 : ℝ)^3209 := by
    have hnat : (5374370829 : ℕ)^4233*12500000000000^3209 ≤ 5510417542797^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374370829 10000000000 5510417542797 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374370193/10000000000 : ℝ)^4233 ≤ (22041666730443/50000000000000 : ℝ)^3209 := by
    have hnat : (5374370193 : ℕ)^4233*50000000000000^3209 ≤ 22041666730443^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374370193 10000000000 22041666730443 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1983035367/10000000000 : ℝ), (5374370829/10000000000 : ℝ), (5374370193/10000000000 : ℝ)] ![(5916663091427/50000000000000 : ℝ), (5510417542797/12500000000000 : ℝ), (22041666730443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1983035367/10000000000 : ℝ)|^4233 ≤ (5916663091427/50000000000000 : ℝ)^3209
        have hw : |(-1983035367/10000000000 : ℝ)|=(1983035367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5374370829/10000000000 : ℝ)|^4233 ≤ (5510417542797/12500000000000 : ℝ)^3209
        have hw : |(5374370829/10000000000 : ℝ)|=(5374370829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374370193/10000000000 : ℝ)|^4233 ≤ (22041666730443/50000000000000 : ℝ)^3209
        have hw : |(5374370193/10000000000 : ℝ)|=(5374370193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_1 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5296999777/10000000000 : ℝ)*x 0 + (-2088262193/10000000000 : ℝ)*x 1 + (5374370563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296999777/10000000000 : ℝ)^4233 ≤ (43248118327409/100000000000000 : ℝ)^3209 := by
    have hnat : (5296999777 : ℕ)^4233*100000000000000^3209 ≤ 43248118327409^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296999777 10000000000 43248118327409 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2088262193/10000000000 : ℝ)^4233 ≤ (6334272094791/50000000000000 : ℝ)^3209 := by
    have hnat : (2088262193 : ℕ)^4233*50000000000000^3209 ≤ 6334272094791^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088262193 10000000000 6334272094791 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5374370563/10000000000 : ℝ)^4233 ≤ (44083337464269/100000000000000 : ℝ)^3209 := by
    have hnat : (5374370563 : ℕ)^4233*100000000000000^3209 ≤ 44083337464269^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374370563 10000000000 44083337464269 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296999777/10000000000 : ℝ), (-2088262193/10000000000 : ℝ), (5374370563/10000000000 : ℝ)] ![(43248118327409/100000000000000 : ℝ), (6334272094791/50000000000000 : ℝ), (44083337464269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296999777/10000000000 : ℝ)|^4233 ≤ (43248118327409/100000000000000 : ℝ)^3209
        have hw : |(5296999777/10000000000 : ℝ)|=(5296999777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2088262193/10000000000 : ℝ)|^4233 ≤ (6334272094791/50000000000000 : ℝ)^3209
        have hw : |(-2088262193/10000000000 : ℝ)|=(2088262193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5374370563/10000000000 : ℝ)|^4233 ≤ (44083337464269/100000000000000 : ℝ)^3209
        have hw : |(5374370563/10000000000 : ℝ)|=(5374370563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_2 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5297000633/10000000000 : ℝ)*x 0 + (1074874041/2000000000 : ℝ)*x 1 + (-1044130763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5297000633/10000000000 : ℝ)^4233 ≤ (10812031886633/25000000000000 : ℝ)^3209 := by
    have hnat : (5297000633 : ℕ)^4233*25000000000000^3209 ≤ 10812031886633^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5297000633 10000000000 10812031886633 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1074874041/2000000000 : ℝ)^4233 ≤ (1763333343629/4000000000000 : ℝ)^3209 := by
    have hnat : (1074874041 : ℕ)^4233*4000000000000^3209 ≤ 1763333343629^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074874041 2000000000 1763333343629 4000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044130763/5000000000 : ℝ)^4233 ≤ (6334269425991/50000000000000 : ℝ)^3209 := by
    have hnat : (1044130763 : ℕ)^4233*50000000000000^3209 ≤ 6334269425991^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044130763 5000000000 6334269425991 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5297000633/10000000000 : ℝ), (1074874041/2000000000 : ℝ), (-1044130763/5000000000 : ℝ)] ![(10812031886633/25000000000000 : ℝ), (1763333343629/4000000000000 : ℝ), (6334269425991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5297000633/10000000000 : ℝ)|^4233 ≤ (10812031886633/25000000000000 : ℝ)^3209
        have hw : |(5297000633/10000000000 : ℝ)|=(5297000633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1074874041/2000000000 : ℝ)|^4233 ≤ (1763333343629/4000000000000 : ℝ)^3209
        have hw : |(1074874041/2000000000 : ℝ)|=(1074874041/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044130763/5000000000 : ℝ)|^4233 ≤ (6334269425991/50000000000000 : ℝ)^3209
        have hw : |(-1044130763/5000000000 : ℝ)|=(1044130763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_3 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4452770689/10000000000 : ℝ)*x 0 + (2147724219/5000000000 : ℝ)*x 1 + (4295448703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4452770689/10000000000 : ℝ)^4233 ≤ (17197977878413/50000000000000 : ℝ)^3209 := by
    have hnat : (4452770689 : ℕ)^4233*50000000000000^3209 ≤ 17197977878413^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4452770689 10000000000 17197977878413 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147724219/5000000000 : ℝ)^4233 ≤ (4100252597957/12500000000000 : ℝ)^3209 := by
    have hnat : (2147724219 : ℕ)^4233*12500000000000^3209 ≤ 4100252597957^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147724219 5000000000 4100252597957 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4295448703/10000000000 : ℝ)^4233 ≤ (32802023453073/100000000000000 : ℝ)^3209 := by
    have hnat : (4295448703 : ℕ)^4233*100000000000000^3209 ≤ 32802023453073^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4295448703 10000000000 32802023453073 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4452770689/10000000000 : ℝ), (2147724219/5000000000 : ℝ), (4295448703/10000000000 : ℝ)] ![(17197977878413/50000000000000 : ℝ), (4100252597957/12500000000000 : ℝ), (32802023453073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4452770689/10000000000 : ℝ)|^4233 ≤ (17197977878413/50000000000000 : ℝ)^3209
        have hw : |(4452770689/10000000000 : ℝ)|=(4452770689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2147724219/5000000000 : ℝ)|^4233 ≤ (4100252597957/12500000000000 : ℝ)^3209
        have hw : |(2147724219/5000000000 : ℝ)|=(2147724219/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4295448703/10000000000 : ℝ)|^4233 ≤ (32802023453073/100000000000000 : ℝ)^3209
        have hw : |(4295448703/10000000000 : ℝ)|=(4295448703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_4 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-557473291/2500000000 : ℝ)*x 0 + (2641295047/5000000000 : ℝ)*x 1 + (5282590131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (557473291/2500000000 : ℝ)^4233 ≤ (13814012779147/100000000000000 : ℝ)^3209 := by
    have hnat : (557473291 : ℕ)^4233*100000000000000^3209 ≤ 13814012779147^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557473291 2500000000 13814012779147 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641295047/5000000000 : ℝ)^4233 ≤ (10773248350679/25000000000000 : ℝ)^3209 := by
    have hnat : (2641295047 : ℕ)^4233*25000000000000^3209 ≤ 10773248350679^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641295047 5000000000 10773248350679 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282590131/10000000000 : ℝ)^4233 ≤ (2154649690043/5000000000000 : ℝ)^3209 := by
    have hnat : (5282590131 : ℕ)^4233*5000000000000^3209 ≤ 2154649690043^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282590131 10000000000 2154649690043 5000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-557473291/2500000000 : ℝ), (2641295047/5000000000 : ℝ), (5282590131/10000000000 : ℝ)] ![(13814012779147/100000000000000 : ℝ), (10773248350679/25000000000000 : ℝ), (2154649690043/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-557473291/2500000000 : ℝ)|^4233 ≤ (13814012779147/100000000000000 : ℝ)^3209
        have hw : |(-557473291/2500000000 : ℝ)|=(557473291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641295047/5000000000 : ℝ)|^4233 ≤ (10773248350679/25000000000000 : ℝ)^3209
        have hw : |(2641295047/5000000000 : ℝ)|=(2641295047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282590131/10000000000 : ℝ)|^4233 ≤ (2154649690043/5000000000000 : ℝ)^3209
        have hw : |(5282590131/10000000000 : ℝ)|=(5282590131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_5 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072330999/2000000000 : ℝ)*x 0 + (-84989271/400000000 : ℝ)*x 1 + (1056518031/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072330999/2000000000 : ℝ)^4233 ≤ (43945807568769/100000000000000 : ℝ)^3209 := by
    have hnat : (1072330999 : ℕ)^4233*100000000000000^3209 ≤ 43945807568769^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072330999 2000000000 43945807568769 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84989271/400000000 : ℝ)^4233 ≤ (6480599179429/50000000000000 : ℝ)^3209 := by
    have hnat : (84989271 : ℕ)^4233*50000000000000^3209 ≤ 6480599179429^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84989271 400000000 6480599179429 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1056518031/2000000000 : ℝ)^4233 ≤ (10773248514779/25000000000000 : ℝ)^3209 := by
    have hnat : (1056518031 : ℕ)^4233*25000000000000^3209 ≤ 10773248514779^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056518031 2000000000 10773248514779 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072330999/2000000000 : ℝ), (-84989271/400000000 : ℝ), (1056518031/2000000000 : ℝ)] ![(43945807568769/100000000000000 : ℝ), (6480599179429/50000000000000 : ℝ), (10773248514779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072330999/2000000000 : ℝ)|^4233 ≤ (43945807568769/100000000000000 : ℝ)^3209
        have hw : |(1072330999/2000000000 : ℝ)|=(1072330999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84989271/400000000 : ℝ)|^4233 ≤ (6480599179429/50000000000000 : ℝ)^3209
        have hw : |(-84989271/400000000 : ℝ)|=(84989271/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1056518031/2000000000 : ℝ)|^4233 ≤ (10773248514779/25000000000000 : ℝ)^3209
        have hw : |(1056518031/2000000000 : ℝ)|=(1056518031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_6 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214466203/400000000 : ℝ)*x 0 + (5282590071/10000000000 : ℝ)*x 1 + (-106236589/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214466203/400000000 : ℝ)^4233 ≤ (43945808433711/100000000000000 : ℝ)^3209 := by
    have hnat : (214466203 : ℕ)^4233*100000000000000^3209 ≤ 43945808433711^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214466203 400000000 43945808433711 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5282590071/10000000000 : ℝ)^4233 ≤ (21546496577611/50000000000000 : ℝ)^3209 := by
    have hnat : (5282590071 : ℕ)^4233*50000000000000^3209 ≤ 21546496577611^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282590071 10000000000 21546496577611 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106236589/500000000 : ℝ)^4233 ≤ (12961198399091/100000000000000 : ℝ)^3209 := by
    have hnat : (106236589 : ℕ)^4233*100000000000000^3209 ≤ 12961198399091^3209*500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106236589 500000000 12961198399091 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214466203/400000000 : ℝ), (5282590071/10000000000 : ℝ), (-106236589/500000000 : ℝ)] ![(43945808433711/100000000000000 : ℝ), (21546496577611/50000000000000 : ℝ), (12961198399091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214466203/400000000 : ℝ)|^4233 ≤ (43945808433711/100000000000000 : ℝ)^3209
        have hw : |(214466203/400000000 : ℝ)|=(214466203/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5282590071/10000000000 : ℝ)|^4233 ≤ (21546496577611/50000000000000 : ℝ)^3209
        have hw : |(5282590071/10000000000 : ℝ)|=(5282590071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-106236589/500000000 : ℝ)|^4233 ≤ (12961198399091/100000000000000 : ℝ)^3209
        have hw : |(-106236589/500000000 : ℝ)|=(106236589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_7 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2119948401/5000000000 : ℝ)*x 0 + (4401865559/10000000000 : ℝ)*x 1 + (4401865701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119948401/5000000000 : ℝ)^4233 ≤ (32243592014581/100000000000000 : ℝ)^3209 := by
    have hnat : (2119948401 : ℕ)^4233*100000000000000^3209 ≤ 32243592014581^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119948401 5000000000 32243592014581 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4401865559/10000000000 : ℝ)^4233 ≤ (33878203267109/100000000000000 : ℝ)^3209 := by
    have hnat : (4401865559 : ℕ)^4233*100000000000000^3209 ≤ 33878203267109^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401865559 10000000000 33878203267109 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4401865701/10000000000 : ℝ)^4233 ≤ (4234775588591/12500000000000 : ℝ)^3209 := by
    have hnat : (4401865701 : ℕ)^4233*12500000000000^3209 ≤ 4234775588591^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4401865701 10000000000 4234775588591 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2119948401/5000000000 : ℝ), (4401865559/10000000000 : ℝ), (4401865701/10000000000 : ℝ)] ![(32243592014581/100000000000000 : ℝ), (33878203267109/100000000000000 : ℝ), (4234775588591/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2119948401/5000000000 : ℝ)|^4233 ≤ (32243592014581/100000000000000 : ℝ)^3209
        have hw : |(2119948401/5000000000 : ℝ)|=(2119948401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4401865559/10000000000 : ℝ)|^4233 ≤ (33878203267109/100000000000000 : ℝ)^3209
        have hw : |(4401865559/10000000000 : ℝ)|=(4401865559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4401865701/10000000000 : ℝ)|^4233 ≤ (4234775588591/12500000000000 : ℝ)^3209
        have hw : |(4401865701/10000000000 : ℝ)|=(4401865701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_8 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089066727/5000000000 : ℝ)*x 0 + (5219928903/10000000000 : ℝ)*x 1 + (1076796743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089066727/5000000000 : ℝ)^4233 ≤ (6696310424339/50000000000000 : ℝ)^3209 := by
    have hnat : (1089066727 : ℕ)^4233*50000000000000^3209 ≤ 6696310424339^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089066727 5000000000 6696310424339 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219928903/10000000000 : ℝ)^4233 ≤ (10604999534997/25000000000000 : ℝ)^3209 := by
    have hnat : (5219928903 : ℕ)^4233*25000000000000^3209 ≤ 10604999534997^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219928903 10000000000 10604999534997 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1076796743/2000000000 : ℝ)^4233 ≤ (1380855656193/3125000000000 : ℝ)^3209 := by
    have hnat : (1076796743 : ℕ)^4233*3125000000000^3209 ≤ 1380855656193^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076796743 2000000000 1380855656193 3125000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089066727/5000000000 : ℝ), (5219928903/10000000000 : ℝ), (1076796743/2000000000 : ℝ)] ![(6696310424339/50000000000000 : ℝ), (10604999534997/25000000000000 : ℝ), (1380855656193/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089066727/5000000000 : ℝ)|^4233 ≤ (6696310424339/50000000000000 : ℝ)^3209
        have hw : |(-1089066727/5000000000 : ℝ)|=(1089066727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219928903/10000000000 : ℝ)|^4233 ≤ (10604999534997/25000000000000 : ℝ)^3209
        have hw : |(5219928903/10000000000 : ℝ)|=(5219928903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1076796743/2000000000 : ℝ)|^4233 ≤ (1380855656193/3125000000000 : ℝ)^3209
        have hw : |(1076796743/2000000000 : ℝ)|=(1076796743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_9 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (211609047/400000000 : ℝ)*x 0 + (-41687511/200000000 : ℝ)*x 1 + (5383982471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211609047/400000000 : ℝ)^4233 ≤ (43175181503909/100000000000000 : ℝ)^3209 := by
    have hnat : (211609047 : ℕ)^4233*100000000000000^3209 ≤ 43175181503909^3209*400000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211609047 400000000 43175181503909 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41687511/200000000 : ℝ)^4233 ≤ (12637450958967/100000000000000 : ℝ)^3209 := by
    have hnat : (41687511 : ℕ)^4233*100000000000000^3209 ≤ 12637450958967^3209*200000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41687511 200000000 12637450958967 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5383982471/10000000000 : ℝ)^4233 ≤ (1767494701219/4000000000000 : ℝ)^3209 := by
    have hnat : (5383982471 : ℕ)^4233*4000000000000^3209 ≤ 1767494701219^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5383982471 10000000000 1767494701219 4000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211609047/400000000 : ℝ), (-41687511/200000000 : ℝ), (5383982471/10000000000 : ℝ)] ![(43175181503909/100000000000000 : ℝ), (12637450958967/100000000000000 : ℝ), (1767494701219/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211609047/400000000 : ℝ)|^4233 ≤ (43175181503909/100000000000000 : ℝ)^3209
        have hw : |(211609047/400000000 : ℝ)|=(211609047/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41687511/200000000 : ℝ)|^4233 ≤ (12637450958967/100000000000000 : ℝ)^3209
        have hw : |(-41687511/200000000 : ℝ)|=(41687511/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5383982471/10000000000 : ℝ)|^4233 ≤ (1767494701219/4000000000000 : ℝ)^3209
        have hw : |(5383982471/10000000000 : ℝ)|=(5383982471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_10 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322556487/2500000000 : ℝ)*x 0 + (1345995939/2500000000 : ℝ)*x 1 + (-416874823/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322556487/2500000000 : ℝ)^4233 ≤ (10793794765029/25000000000000 : ℝ)^3209 := by
    have hnat : (1322556487 : ℕ)^4233*25000000000000^3209 ≤ 10793794765029^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322556487 2500000000 10793794765029 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1345995939/2500000000 : ℝ)^4233 ≤ (44187381442047/100000000000000 : ℝ)^3209 := by
    have hnat : (1345995939 : ℕ)^4233*100000000000000^3209 ≤ 44187381442047^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345995939 2500000000 44187381442047 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416874823/2000000000 : ℝ)^4233 ≤ (252748789647/2000000000000 : ℝ)^3209 := by
    have hnat : (416874823 : ℕ)^4233*2000000000000^3209 ≤ 252748789647^3209*2000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416874823 2000000000 252748789647 2000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322556487/2500000000 : ℝ), (1345995939/2500000000 : ℝ), (-416874823/2000000000 : ℝ)] ![(10793794765029/25000000000000 : ℝ), (44187381442047/100000000000000 : ℝ), (252748789647/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322556487/2500000000 : ℝ)|^4233 ≤ (10793794765029/25000000000000 : ℝ)^3209
        have hw : |(1322556487/2500000000 : ℝ)|=(1322556487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1345995939/2500000000 : ℝ)|^4233 ≤ (44187381442047/100000000000000 : ℝ)^3209
        have hw : |(1345995939/2500000000 : ℝ)|=(1345995939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416874823/2000000000 : ℝ)|^4233 ≤ (252748789647/2000000000000 : ℝ)^3209
        have hw : |(-416874823/2000000000 : ℝ)|=(416874823/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_11 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (223739731/500000000 : ℝ)*x 0 + (4284296393/10000000000 : ℝ)*x 1 + (1071073939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223739731/500000000 : ℝ)^4233 ≤ (17310273456117/50000000000000 : ℝ)^3209 := by
    have hnat : (223739731 : ℕ)^4233*50000000000000^3209 ≤ 17310273456117^3209*500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223739731 500000000 17310273456117 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4284296393/10000000000 : ℝ)^4233 ≤ (32689729741973/100000000000000 : ℝ)^3209 := by
    have hnat : (4284296393 : ℕ)^4233*100000000000000^3209 ≤ 32689729741973^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284296393 10000000000 32689729741973 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1071073939/2500000000 : ℝ)^4233 ≤ (16344861665309/50000000000000 : ℝ)^3209 := by
    have hnat : (1071073939 : ℕ)^4233*50000000000000^3209 ≤ 16344861665309^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071073939 2500000000 16344861665309 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(223739731/500000000 : ℝ), (4284296393/10000000000 : ℝ), (1071073939/2500000000 : ℝ)] ![(17310273456117/50000000000000 : ℝ), (32689729741973/100000000000000 : ℝ), (16344861665309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(223739731/500000000 : ℝ)|^4233 ≤ (17310273456117/50000000000000 : ℝ)^3209
        have hw : |(223739731/500000000 : ℝ)|=(223739731/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4284296393/10000000000 : ℝ)|^4233 ≤ (32689729741973/100000000000000 : ℝ)^3209
        have hw : |(4284296393/10000000000 : ℝ)|=(4284296393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1071073939/2500000000 : ℝ)|^4233 ≤ (16344861665309/50000000000000 : ℝ)^3209
        have hw : |(1071073939/2500000000 : ℝ)|=(1071073939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_12 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2035037651/10000000000 : ℝ)*x 0 + (5435842931/10000000000 : ℝ)*x 1 + (5274500119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2035037651/10000000000 : ℝ)^4233 ≤ (12244362307849/100000000000000 : ℝ)^3209 := by
    have hnat : (2035037651 : ℕ)^4233*100000000000000^3209 ≤ 12244362307849^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2035037651 10000000000 12244362307849 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435842931/10000000000 : ℝ)^4233 ≤ (44749676346101/100000000000000 : ℝ)^3209 := by
    have hnat : (5435842931 : ℕ)^4233*100000000000000^3209 ≤ 44749676346101^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435842931 10000000000 44749676346101 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274500119/10000000000 : ℝ)^4233 ≤ (2687872583279/6250000000000 : ℝ)^3209 := by
    have hnat : (5274500119 : ℕ)^4233*6250000000000^3209 ≤ 2687872583279^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274500119 10000000000 2687872583279 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2035037651/10000000000 : ℝ), (5435842931/10000000000 : ℝ), (5274500119/10000000000 : ℝ)] ![(12244362307849/100000000000000 : ℝ), (44749676346101/100000000000000 : ℝ), (2687872583279/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2035037651/10000000000 : ℝ)|^4233 ≤ (12244362307849/100000000000000 : ℝ)^3209
        have hw : |(-2035037651/10000000000 : ℝ)|=(2035037651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435842931/10000000000 : ℝ)|^4233 ≤ (44749676346101/100000000000000 : ℝ)^3209
        have hw : |(5435842931/10000000000 : ℝ)|=(5435842931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274500119/10000000000 : ℝ)|^4233 ≤ (2687872583279/6250000000000 : ℝ)^3209
        have hw : |(5274500119/10000000000 : ℝ)|=(5274500119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_13 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5367352459/10000000000 : ℝ)*x 0 + (-106394541/500000000 : ℝ)*x 1 + (2637249899/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367352459/10000000000 : ℝ)^4233 ≤ (8801483545673/20000000000000 : ℝ)^3209 := by
    have hnat : (5367352459 : ℕ)^4233*20000000000000^3209 ≤ 8801483545673^3209*10000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367352459 10000000000 8801483545673 20000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106394541/500000000 : ℝ)^4233 ≤ (12986624378883/100000000000000 : ℝ)^3209 := by
    have hnat : (106394541 : ℕ)^4233*100000000000000^3209 ≤ 12986624378883^3209*500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106394541 500000000 12986624378883 100000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2637249899/5000000000 : ℝ)^4233 ≤ (21502978939993/50000000000000 : ℝ)^3209 := by
    have hnat : (2637249899 : ℕ)^4233*50000000000000^3209 ≤ 21502978939993^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637249899 5000000000 21502978939993 50000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367352459/10000000000 : ℝ), (-106394541/500000000 : ℝ), (2637249899/5000000000 : ℝ)] ![(8801483545673/20000000000000 : ℝ), (12986624378883/100000000000000 : ℝ), (21502978939993/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367352459/10000000000 : ℝ)|^4233 ≤ (8801483545673/20000000000000 : ℝ)^3209
        have hw : |(5367352459/10000000000 : ℝ)|=(5367352459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106394541/500000000 : ℝ)|^4233 ≤ (12986624378883/100000000000000 : ℝ)^3209
        have hw : |(-106394541/500000000 : ℝ)|=(106394541/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2637249899/5000000000 : ℝ)|^4233 ≤ (21502978939993/50000000000000 : ℝ)^3209
        have hw : |(2637249899/5000000000 : ℝ)|=(2637249899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_14 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1341838099/2500000000 : ℝ)*x 0 + (2637249957/5000000000 : ℝ)*x 1 + (-8511563/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1341838099/2500000000 : ℝ)^4233 ≤ (2750463565437/6250000000000 : ℝ)^3209 := by
    have hnat : (1341838099 : ℕ)^4233*6250000000000^3209 ≤ 2750463565437^3209*2500000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1341838099 2500000000 2750463565437 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2637249957/5000000000 : ℝ)^4233 ≤ (4300595912761/10000000000000 : ℝ)^3209 := by
    have hnat : (2637249957 : ℕ)^4233*10000000000000^3209 ≤ 4300595912761^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637249957 5000000000 4300595912761 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8511563/40000000 : ℝ)^4233 ≤ (811663988459/6250000000000 : ℝ)^3209 := by
    have hnat : (8511563 : ℕ)^4233*6250000000000^3209 ≤ 811663988459^3209*40000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8511563 40000000 811663988459 6250000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1341838099/2500000000 : ℝ), (2637249957/5000000000 : ℝ), (-8511563/40000000 : ℝ)] ![(2750463565437/6250000000000 : ℝ), (4300595912761/10000000000000 : ℝ), (811663988459/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1341838099/2500000000 : ℝ)|^4233 ≤ (2750463565437/6250000000000 : ℝ)^3209
        have hw : |(1341838099/2500000000 : ℝ)|=(1341838099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2637249957/5000000000 : ℝ)|^4233 ≤ (4300595912761/10000000000000 : ℝ)^3209
        have hw : |(2637249957/5000000000 : ℝ)|=(2637249957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8511563/40000000 : ℝ)|^4233 ≤ (811663988459/6250000000000 : ℝ)^3209
        have hw : |(-8511563/40000000 : ℝ)|=(8511563/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1272_box_15 (p : ℝ) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84418009/200000000 : ℝ)*x 0 + (2205620461/5000000000 : ℝ)*x 1 + (441124099/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84418009/200000000 : ℝ)^4233 ≤ (8013291529633/25000000000000 : ℝ)^3209 := by
    have hnat : (84418009 : ℕ)^4233*25000000000000^3209 ≤ 8013291529633^3209*200000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84418009 200000000 8013291529633 25000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205620461/5000000000 : ℝ)^4233 ≤ (4246677073831/12500000000000 : ℝ)^3209 := by
    have hnat : (2205620461 : ℕ)^4233*12500000000000^3209 ≤ 4246677073831^3209*5000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205620461 5000000000 4246677073831 12500000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441124099/1000000000 : ℝ)^4233 ≤ (3397341728147/10000000000000 : ℝ)^3209 := by
    have hnat : (441124099 : ℕ)^4233*10000000000000^3209 ≤ 3397341728147^3209*1000000000^4233 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441124099 1000000000 3397341728147 10000000000000 4233 3209 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4233/1024 : ℝ)) 4233 3209 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84418009/200000000 : ℝ), (2205620461/5000000000 : ℝ), (441124099/1000000000 : ℝ)] ![(8013291529633/25000000000000 : ℝ), (4246677073831/12500000000000 : ℝ), (3397341728147/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84418009/200000000 : ℝ)|^4233 ≤ (8013291529633/25000000000000 : ℝ)^3209
        have hw : |(84418009/200000000 : ℝ)|=(84418009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205620461/5000000000 : ℝ)|^4233 ≤ (4246677073831/12500000000000 : ℝ)^3209
        have hw : |(2205620461/5000000000 : ℝ)|=(2205620461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(441124099/1000000000 : ℝ)|^4233 ≤ (3397341728147/10000000000000 : ℝ)^3209
        have hw : |(441124099/1000000000 : ℝ)|=(441124099/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1272_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62253/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29701/50000 : ℝ) ∧ (401/500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83413/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2879/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (353/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2879/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2879/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (353/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2879/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2879/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (353/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2879/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2879/25000 : ℝ) ^ (8465/2048 : ℝ) ≤ (6592458530591287/50000000000000000000 : ℝ) := by
    have hpowers : (2879/25000 : ℝ)^8465 ≤ (6592458530591287/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2879 : ℕ)^8465*50000000000000000000^2048 ≤ 6592458530591287^2048*25000^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2879 25000 6592458530591287 50000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2879/25000 : ℝ)) (X := (6592458530591287/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (353/2500 : ℝ) ^ (8465/2048 : ℝ) ≤ (30620416080645321/100000000000000000000 : ℝ) := by
    have hpowers : (353/2500 : ℝ)^8465 ≤ (30620416080645321/100000000000000000000 : ℝ)^2048 := by
      have hnat : (353 : ℕ)^8465*100000000000000000000^2048 ≤ 30620416080645321^2048*2500^8465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        353 2500 30620416080645321 100000000000000000000 8465 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (353/2500 : ℝ)) (X := (30620416080645321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006592458530591287/25000000000000000000 : ℝ) ≤ (5000318960562781/5000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (25006592458530591287/25000000000000000000 : ℝ)^2048 ≤ (5000318960562781/5000000000000000 : ℝ)^8465 := by
      have hnat : (25006592458530591287 : ℕ)^2048*5000000000000000^8465 ≤ 5000318960562781^8465*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006592458530591287 25000000000000000000 5000318960562781 5000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000318960562781/5000000000000000 : ℝ)) (X := (25006592458530591287/25000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008761066628365579/20000000000000000000 : ℝ) ≤ (1250132454858923/1250000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (20008761066628365579/20000000000000000000 : ℝ)^2048 ≤ (1250132454858923/1250000000000000 : ℝ)^8465 := by
      have hnat : (20008761066628365579 : ℕ)^2048*1250000000000000^8465 ≤ 1250132454858923^8465*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008761066628365579 20000000000000000000 1250132454858923 1250000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250132454858923/1250000000000000 : ℝ)) (X := (20008761066628365579/20000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030620416080645321/50000000000000000000 : ℝ) ≤ (5000740678308603/5000000000000000 : ℝ) ^ (8465/2048 : ℝ) := by
    have hpowers : (50030620416080645321/50000000000000000000 : ℝ)^2048 ≤ (5000740678308603/5000000000000000 : ℝ)^8465 := by
      have hnat : (50030620416080645321 : ℕ)^2048*5000000000000000^8465 ≤ 5000740678308603^8465*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030620416080645321 50000000000000000000 5000740678308603 5000000000000000 2048 8465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000740678308603/5000000000000000 : ℝ)) (X := (50030620416080645321/50000000000000000000 : ℝ)) (by norm_num) 8465 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6592458530591287/50000000000000000000 : ℝ) ≤ ((3253993517936148893/3255000000000000000 : ℝ)+2*(210858872911/130200000000000 : ℝ)*(2879/25000 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (3253993517936148893/3255000000000000000 : ℝ)+2*(210858872911/130200000000000 : ℝ)*(2879/25000 : ℝ)=(5000318960562781/5000000000000000 : ℝ) by norm_num, show 1+2*(6592458530591287/50000000000000000000 : ℝ)=(25006592458530591287/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30620416080645321/100000000000000000000 : ℝ)+(6592458530591287/50000000000000000000 : ℝ) ≤ ((3253993517936148893/3255000000000000000 : ℝ)+(210858872911/130200000000000 : ℝ)*((353/2500 : ℝ)+(2879/25000 : ℝ)))^(8465/2048 : ℝ) := by
    rw [show (3253993517936148893/3255000000000000000 : ℝ)+(210858872911/130200000000000 : ℝ)*((353/2500 : ℝ)+(2879/25000 : ℝ))=(1250132454858923/1250000000000000 : ℝ) by norm_num, show 1+(30620416080645321/100000000000000000000 : ℝ)+(6592458530591287/50000000000000000000 : ℝ)=(20008761066628365579/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30620416080645321/100000000000000000000 : ℝ) ≤ ((3253993517936148893/3255000000000000000 : ℝ)+2*(210858872911/130200000000000 : ℝ)*(353/2500 : ℝ))^(8465/2048 : ℝ) := by
    rw [show (3253993517936148893/3255000000000000000 : ℝ)+2*(210858872911/130200000000000 : ℝ)*(353/2500 : ℝ)=(5000740678308603/5000000000000000 : ℝ) by norm_num, show 1+2*(30620416080645321/100000000000000000000 : ℝ)=(50030620416080645321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3253993517936148893/3255000000000000000 : ℝ)*(X 1 0+X 2 0)+(210858872911/130200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (2879/25000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (3253993517936148893/3255000000000000000 : ℝ)) (alpha := (210858872911/130200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3253993517936148893/3255000000000000000 : ℝ)*(X 0 1+X 2 1)+(210858872911/130200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (2879/25000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (3253993517936148893/3255000000000000000 : ℝ)) (alpha := (210858872911/130200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3253993517936148893/3255000000000000000 : ℝ)*(X 0 2+X 1 2)+(210858872911/130200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8465/2048 : ℝ)) (lo := (2879/25000 : ℝ)) (hi := (353/2500 : ℝ)) (c := (3253993517936148893/3255000000000000000 : ℝ)) (alpha := (210858872911/130200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1983035367/10000000000 : ℝ)*X 0 0+(5374370829/10000000000 : ℝ)*X 0 1+(5374370193/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296999777/10000000000 : ℝ)*X 1 0+(-2088262193/10000000000 : ℝ)*X 1 1+(5374370563/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5297000633/10000000000 : ℝ)*X 2 0+(1074874041/2000000000 : ℝ)*X 2 1+(-1044130763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4452770689/10000000000 : ℝ)*X 0 0+(2147724219/5000000000 : ℝ)*X 0 1+(4295448703/10000000000 : ℝ)*X 0 2+(4452770689/10000000000 : ℝ)*X 1 0+(2147724219/5000000000 : ℝ)*X 1 1+(4295448703/10000000000 : ℝ)*X 1 2+(4452770689/10000000000 : ℝ)*X 2 0+(2147724219/5000000000 : ℝ)*X 2 1+(4295448703/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-557473291/2500000000 : ℝ)*X 0 0+(2641295047/5000000000 : ℝ)*X 0 1+(5282590131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072330999/2000000000 : ℝ)*X 1 0+(-84989271/400000000 : ℝ)*X 1 1+(1056518031/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((214466203/400000000 : ℝ)*X 2 0+(5282590071/10000000000 : ℝ)*X 2 1+(-106236589/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2119948401/5000000000 : ℝ)*X 0 0+(4401865559/10000000000 : ℝ)*X 0 1+(4401865701/10000000000 : ℝ)*X 0 2+(2119948401/5000000000 : ℝ)*X 1 0+(4401865559/10000000000 : ℝ)*X 1 1+(4401865701/10000000000 : ℝ)*X 1 2+(2119948401/5000000000 : ℝ)*X 2 0+(4401865559/10000000000 : ℝ)*X 2 1+(4401865701/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1089066727/5000000000 : ℝ)*X 0 0+(5219928903/10000000000 : ℝ)*X 0 1+(1076796743/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((211609047/400000000 : ℝ)*X 1 0+(-41687511/200000000 : ℝ)*X 1 1+(5383982471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1322556487/2500000000 : ℝ)*X 2 0+(1345995939/2500000000 : ℝ)*X 2 1+(-416874823/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((223739731/500000000 : ℝ)*X 0 0+(4284296393/10000000000 : ℝ)*X 0 1+(1071073939/2500000000 : ℝ)*X 0 2+(223739731/500000000 : ℝ)*X 1 0+(4284296393/10000000000 : ℝ)*X 1 1+(1071073939/2500000000 : ℝ)*X 1 2+(223739731/500000000 : ℝ)*X 2 0+(4284296393/10000000000 : ℝ)*X 2 1+(1071073939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2035037651/10000000000 : ℝ)*X 0 0+(5435842931/10000000000 : ℝ)*X 0 1+(5274500119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367352459/10000000000 : ℝ)*X 1 0+(-106394541/500000000 : ℝ)*X 1 1+(2637249899/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1341838099/2500000000 : ℝ)*X 2 0+(2637249957/5000000000 : ℝ)*X 2 1+(-8511563/40000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((84418009/200000000 : ℝ)*X 0 0+(2205620461/5000000000 : ℝ)*X 0 1+(441124099/1000000000 : ℝ)*X 0 2+(84418009/200000000 : ℝ)*X 1 0+(2205620461/5000000000 : ℝ)*X 1 1+(441124099/1000000000 : ℝ)*X 1 2+(84418009/200000000 : ℝ)*X 2 0+(2205620461/5000000000 : ℝ)*X 2 1+(441124099/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1272_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62253/100000 : ℝ) ≤ (-1688544035258603695935467594831/2712500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14906489/50000000000000 : ℝ)*(upper0) + (244437/1250000000000 : ℝ)*(upper1) + (322589/10000000000000 : ℝ)*(upper2) + (4072803/12500000000000 : ℝ)*(upper3) + (41775657/50000000000000 : ℝ)*(upper5) + (402854237779433/10000000000000 : ℝ)*(major0) + (402854237779433/10000000000000 : ℝ)*(major1) + (402854237779433/10000000000000 : ℝ)*(major2) + (7215395059/100000000000000 : ℝ)*(sp2) + (622493393/12500000000000 : ℝ)*(sp3) + (5428105582950771/100000000000000 : ℝ)*(sp4) + (5428105582950771/100000000000000 : ℝ)*(sp5) + (42407018496529/781250000000 : ℝ)*(sp6) + (264972434980601/10000000000000 : ℝ)*(sp7) + (41402020777393/1562500000000 : ℝ)*(f.failure) + (5428105582950771/100000000000000 : ℝ)*(f.sum) + (3078462088129/651000000000000000000000000 : ℝ)*base66 + (85569972203035777/10850000000000000000000000000000 : ℝ)*base68 + (822584704613985777/10850000000000000000000000000000 : ℝ)*base70 + (116310845861285777/10850000000000000000000000000000 : ℝ)*base72 + (97898967931/162750000000000000000000000 : ℝ)*base74 + (327614914617614223/10850000000000000000000000000000 : ℝ)*base75 + (173673272542985777/10850000000000000000000000000000 : ℝ)*base78 + (1571695450580085777/10850000000000000000000000000000 : ℝ)*base80 + (18155439869683/130200000000000000000000000 : ℝ)*base81 + (396643/39062500000000000000 : ℝ)*base90 + (396643/39062500000000000000 : ℝ)*base92 + (396643/39062500000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (29701/50000 : ℝ) ≤ (322271845189849423999573299/542500000000000000000000000 : ℝ) := by norm_num
    linear_combination (78582501/50000000000000 : ℝ)*(upper0) + (5182339/2500000000000 : ℝ)*(lower1) + (596480013/100000000000000 : ℝ)*(upper4) + (2047428503323089/50000000000000 : ℝ)*(major0) + (2047428503323089/50000000000000 : ℝ)*(major1) + (2047428503323089/50000000000000 : ℝ)*(major2) + (5476543303682783/100000000000000 : ℝ)*(sp0) + (2738269225582693/50000000000000 : ℝ)*(sp1) + (684568547985997/12500000000000 : ℝ)*(sp2) + (336666423440229/12500000000000 : ℝ)*(sp3) + (8467121877/50000000000000 : ℝ)*(sp6) + (3131632951/20000000000000 : ℝ)*(sp7) + (5503612237/25000000000000 : ℝ)*(sp8) + (3358370793/12500000000000 : ℝ)*(sp9) + (2693347045686587/100000000000000 : ℝ)*(f.failure) + (547656531813173/10000000000000 : ℝ)*(f.sum) + (309957805067/271250000000000000000000000 : ℝ)*base65 + (74293668512555159/54250000000000000000000000000000 : ℝ)*base67 + (202498971418944841/54250000000000000000000000000000 : ℝ)*base70 + (84247414026444841/54250000000000000000000000000000 : ℝ)*base72 + (7716885551419/542500000000000000000000000 : ℝ)*base73 + (785256850968305159/54250000000000000000000000000000 : ℝ)*base75 + (78240161579444841/54250000000000000000000000000000 : ℝ)*base78 + (587583273394805159/54250000000000000000000000000000 : ℝ)*base79 + (1929437020009/542500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (10403587/2500000000000000000000 : ℝ)*base90 + (10403587/2500000000000000000000 : ℝ)*base92 + (10403587/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (401/500 : ℝ) ≤ (870195636895353791330946681/1085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3000289/12500000000000 : ℝ)*(upper1) + (69680269/10000000000000 : ℝ)*(lower3) + (614869789/100000000000000 : ℝ)*(upper4) + (210678779/50000000000000 : ℝ)*(lower5) + (2280604290200693/50000000000000 : ℝ)*(major0) + (2280604290200693/50000000000000 : ℝ)*(major1) + (2280604290200693/50000000000000 : ℝ)*(major2) + (38994491767/100000000000000 : ℝ)*(sp0) + (1111844862831/100000000000000 : ℝ)*(sp2) + (110009735211/20000000000000 : ℝ)*(sp3) + (1219111878818371/20000000000000 : ℝ)*(sp8) + (3047799194291811/50000000000000 : ℝ)*(sp9) + (6094486543720791/100000000000000 : ℝ)*(sp10) + (93735456331059/3125000000000 : ℝ)*(sp11) + (375010581408743/12500000000000 : ℝ)*(f.failure) + (3047799194291811/50000000000000 : ℝ)*(f.sum) + (2807207821343/3255000000000000000000000000 : ℝ)*base65 + (199598006795880717/54250000000000000000000000000000 : ℝ)*base68 + (4267692003294369283/54250000000000000000000000000000 : ℝ)*base69 + (315871615318630717/54250000000000000000000000000000 : ℝ)*base72 + (6579550431953/3255000000000000000000000000 : ℝ)*base73 + (2689947520668869283/54250000000000000000000000000000 : ℝ)*base75 + (208196890707119283/54250000000000000000000000000000 : ℝ)*base77 + (101132707578630717/54250000000000000000000000000000 : ℝ)*base80 + (792331261226213/3255000000000000000000000000 : ℝ)*base81 + (28257/312500000000000000000 : ℝ)*base89 + (28257/312500000000000000000 : ℝ)*base91 + (28257/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83413/100000 : ℝ) ≤ (-258573171668075957743267201/310000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2166457/100000000000000 : ℝ)*(upper1) + (84505727/100000000000000 : ℝ)*(upper3) + (128969683/100000000000000 : ℝ)*(upper5) + (4596876328327717/100000000000000 : ℝ)*(major0) + (4596876328327717/100000000000000 : ℝ)*(major1) + (4596876328327717/100000000000000 : ℝ)*(major2) + (3801469183/12500000000000 : ℝ)*(sp4) + (75620538101/20000000000000 : ℝ)*(sp5) + (30957563121/10000000000000 : ℝ)*(sp6) + (111542928619/50000000000000 : ℝ)*(sp7) + (1549495273139199/25000000000000 : ℝ)*(sp12) + (1239526680323951/20000000000000 : ℝ)*(sp13) + (123954038573581/2000000000000 : ℝ)*(sp14) + (377915204166743/12500000000000 : ℝ)*(sp15) + (1511772359595591/50000000000000 : ℝ)*(f.failure) + (309900575215513/5000000000000 : ℝ)*(f.sum) + (174909280621/930000000000000000000000000 : ℝ)*base65 + (168813557784021061/15500000000000000000000000000000 : ℝ)*base67 + (805903381177978939/15500000000000000000000000000000 : ℝ)*base70 + (41869581422978939/15500000000000000000000000000000 : ℝ)*base72 + (3396154418191/930000000000000000000000000 : ℝ)*base73 + (658884357338521061/15500000000000000000000000000000 : ℝ)*base75 + (9363671637978939/15500000000000000000000000000000 : ℝ)*base78 + (160860152555021061/15500000000000000000000000000000 : ℝ)*base79 + (73196078933399/930000000000000000000000000 : ℝ)*base82 + (3776591/1250000000000000000000 : ℝ)*base90 + (3776591/1250000000000000000000 : ℝ)*base92 + (3776591/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1272_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29701/50000 : ℝ) else (401/500 : ℝ) ≤ X j i ∧ X j i ≤ (83413/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1272_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1272_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29701/50000 : ℝ) else (401/500 : ℝ) ≤ X j i ∧ X j i ≤ (83413/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1272_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8465/2048 : ℝ) ≤ p) (hpb : p ≤ (4233/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (38008999/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (353/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2879/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62253/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29701/50000 : ℝ) else (401/500 : ℝ) ≤ X j i ∧ X j i ≤ (83413/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1272_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
