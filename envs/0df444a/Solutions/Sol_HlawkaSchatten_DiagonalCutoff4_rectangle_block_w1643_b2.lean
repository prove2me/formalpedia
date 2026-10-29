-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1643_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:21.431991+00:00
-- url     : https://prove2.me/submissions/259967ac-8900-4fa7-b34b-1fa98c59ec08

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
theorem support_rectangle_w1643_box_0 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-682054291/5000000000 : ℝ)*x 0 + (676223979/1250000000 : ℝ)*x 1 + (5409792071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (682054291/5000000000 : ℝ)^4891 ≤ (8049201959823/100000000000000 : ℝ)^3867 := by
    have hnat : (682054291 : ℕ)^4891*100000000000000^3867 ≤ 8049201959823^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682054291 5000000000 8049201959823 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676223979/1250000000 : ℝ)^4891 ≤ (11493849430793/25000000000000 : ℝ)^3867 := by
    have hnat : (676223979 : ℕ)^4891*25000000000000^3867 ≤ 11493849430793^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676223979 1250000000 11493849430793 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409792071/10000000000 : ℝ)^4891 ≤ (9195080058437/20000000000000 : ℝ)^3867 := by
    have hnat : (5409792071 : ℕ)^4891*20000000000000^3867 ≤ 9195080058437^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409792071 10000000000 9195080058437 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-682054291/5000000000 : ℝ), (676223979/1250000000 : ℝ), (5409792071/10000000000 : ℝ)] ![(8049201959823/100000000000000 : ℝ), (11493849430793/25000000000000 : ℝ), (9195080058437/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-682054291/5000000000 : ℝ)|^4891 ≤ (8049201959823/100000000000000 : ℝ)^3867
        have hw : |(-682054291/5000000000 : ℝ)|=(682054291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676223979/1250000000 : ℝ)|^4891 ≤ (11493849430793/25000000000000 : ℝ)^3867
        have hw : |(676223979/1250000000 : ℝ)|=(676223979/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409792071/10000000000 : ℝ)|^4891 ≤ (9195080058437/20000000000000 : ℝ)^3867
        have hw : |(5409792071/10000000000 : ℝ)|=(5409792071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_1 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312791991/2500000000 : ℝ)*x 0 + (-1587032177/10000000000 : ℝ)*x 1 + (5409791957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312791991/2500000000 : ℝ)^4891 ≤ (8855403185997/20000000000000 : ℝ)^3867 := by
    have hnat : (1312791991 : ℕ)^4891*20000000000000^3867 ≤ 8855403185997^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312791991 2500000000 8855403185997 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1587032177/10000000000 : ℝ)^4891 ≤ (9747584983441/100000000000000 : ℝ)^3867 := by
    have hnat : (1587032177 : ℕ)^4891*100000000000000^3867 ≤ 9747584983441^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587032177 10000000000 9747584983441 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5409791957/10000000000 : ℝ)^4891 ≤ (22987699533399/50000000000000 : ℝ)^3867 := by
    have hnat : (5409791957 : ℕ)^4891*50000000000000^3867 ≤ 22987699533399^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409791957 10000000000 22987699533399 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312791991/2500000000 : ℝ), (-1587032177/10000000000 : ℝ), (5409791957/10000000000 : ℝ)] ![(8855403185997/20000000000000 : ℝ), (9747584983441/100000000000000 : ℝ), (22987699533399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312791991/2500000000 : ℝ)|^4891 ≤ (8855403185997/20000000000000 : ℝ)^3867
        have hw : |(1312791991/2500000000 : ℝ)|=(1312791991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1587032177/10000000000 : ℝ)|^4891 ≤ (9747584983441/100000000000000 : ℝ)^3867
        have hw : |(-1587032177/10000000000 : ℝ)|=(1587032177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5409791957/10000000000 : ℝ)|^4891 ≤ (22987699533399/50000000000000 : ℝ)^3867
        have hw : |(5409791957/10000000000 : ℝ)|=(5409791957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_2 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1312792057/2500000000 : ℝ)*x 0 + (1352447899/2500000000 : ℝ)*x 1 + (-793516157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312792057/2500000000 : ℝ)^4891 ≤ (5534627343181/12500000000000 : ℝ)^3867 := by
    have hnat : (1312792057 : ℕ)^4891*12500000000000^3867 ≤ 5534627343181^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312792057 2500000000 5534627343181 12500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352447899/2500000000 : ℝ)^4891 ≤ (22987697593203/50000000000000 : ℝ)^3867 := by
    have hnat : (1352447899 : ℕ)^4891*50000000000000^3867 ≤ 22987697593203^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352447899 2500000000 22987697593203 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (793516157/5000000000 : ℝ)^4891 ≤ (243689651193/2500000000000 : ℝ)^3867 := by
    have hnat : (793516157 : ℕ)^4891*2500000000000^3867 ≤ 243689651193^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793516157 5000000000 243689651193 2500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312792057/2500000000 : ℝ), (1352447899/2500000000 : ℝ), (-793516157/5000000000 : ℝ)] ![(5534627343181/12500000000000 : ℝ), (22987697593203/50000000000000 : ℝ), (243689651193/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312792057/2500000000 : ℝ)|^4891 ≤ (5534627343181/12500000000000 : ℝ)^3867
        have hw : |(1312792057/2500000000 : ℝ)|=(1312792057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352447899/2500000000 : ℝ)|^4891 ≤ (22987697593203/50000000000000 : ℝ)^3867
        have hw : |(1352447899/2500000000 : ℝ)|=(1352447899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-793516157/5000000000 : ℝ)|^4891 ≤ (243689651193/2500000000000 : ℝ)^3867
        have hw : |(-793516157/5000000000 : ℝ)|=(793516157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_3 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1115856337/2500000000 : ℝ)*x 0 + (4059647821/10000000000 : ℝ)*x 1 + (31715999/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115856337/2500000000 : ℝ)^4891 ≤ (9012365088137/25000000000000 : ℝ)^3867 := by
    have hnat : (1115856337 : ℕ)^4891*25000000000000^3867 ≤ 9012365088137^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115856337 2500000000 9012365088137 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4059647821/10000000000 : ℝ)^4891 ≤ (15987634781557/50000000000000 : ℝ)^3867 := by
    have hnat : (4059647821 : ℕ)^4891*50000000000000^3867 ≤ 15987634781557^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4059647821 10000000000 15987634781557 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (31715999/78125000 : ℝ)^4891 ≤ (31975270071179/100000000000000 : ℝ)^3867 := by
    have hnat : (31715999 : ℕ)^4891*100000000000000^3867 ≤ 31975270071179^3867*78125000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31715999 78125000 31975270071179 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115856337/2500000000 : ℝ), (4059647821/10000000000 : ℝ), (31715999/78125000 : ℝ)] ![(9012365088137/25000000000000 : ℝ), (15987634781557/50000000000000 : ℝ), (31975270071179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115856337/2500000000 : ℝ)|^4891 ≤ (9012365088137/25000000000000 : ℝ)^3867
        have hw : |(1115856337/2500000000 : ℝ)|=(1115856337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4059647821/10000000000 : ℝ)|^4891 ≤ (15987634781557/50000000000000 : ℝ)^3867
        have hw : |(4059647821/10000000000 : ℝ)|=(4059647821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(31715999/78125000 : ℝ)|^4891 ≤ (31975270071179/100000000000000 : ℝ)^3867
        have hw : |(31715999/78125000 : ℝ)|=(31715999/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_4 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-473943769/2500000000 : ℝ)*x 0 + (1303886211/2500000000 : ℝ)*x 1 + (260777243/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (473943769/2500000000 : ℝ)^4891 ≤ (3051274844149/25000000000000 : ℝ)^3867 := by
    have hnat : (473943769 : ℕ)^4891*25000000000000^3867 ≤ 3051274844149^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473943769 2500000000 3051274844149 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1303886211/2500000000 : ℝ)^4891 ≤ (4389745022119/10000000000000 : ℝ)^3867 := by
    have hnat : (1303886211 : ℕ)^4891*10000000000000^3867 ≤ 4389745022119^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303886211 2500000000 4389745022119 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260777243/500000000 : ℝ)^4891 ≤ (43897450391517/100000000000000 : ℝ)^3867 := by
    have hnat : (260777243 : ℕ)^4891*100000000000000^3867 ≤ 43897450391517^3867*500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260777243 500000000 43897450391517 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-473943769/2500000000 : ℝ), (1303886211/2500000000 : ℝ), (260777243/500000000 : ℝ)] ![(3051274844149/25000000000000 : ℝ), (4389745022119/10000000000000 : ℝ), (43897450391517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-473943769/2500000000 : ℝ)|^4891 ≤ (3051274844149/25000000000000 : ℝ)^3867
        have hw : |(-473943769/2500000000 : ℝ)|=(473943769/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1303886211/2500000000 : ℝ)|^4891 ≤ (4389745022119/10000000000000 : ℝ)^3867
        have hw : |(1303886211/2500000000 : ℝ)|=(1303886211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260777243/500000000 : ℝ)|^4891 ≤ (43897450391517/100000000000000 : ℝ)^3867
        have hw : |(260777243/500000000 : ℝ)|=(260777243/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_5 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384620793/10000000000 : ℝ)*x 0 + (-417532549/2500000000 : ℝ)*x 1 + (5215544967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384620793/10000000000 : ℝ)^4891 ≤ (45705000866503/100000000000000 : ℝ)^3867 := by
    have hnat : (5384620793 : ℕ)^4891*100000000000000^3867 ≤ 45705000866503^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384620793 10000000000 45705000866503 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417532549/2500000000 : ℝ)^4891 ≤ (2599386896939/25000000000000 : ℝ)^3867 := by
    have hnat : (417532549 : ℕ)^4891*25000000000000^3867 ≤ 2599386896939^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417532549 2500000000 2599386896939 25000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215544967/10000000000 : ℝ)^4891 ≤ (21948725765289/50000000000000 : ℝ)^3867 := by
    have hnat : (5215544967 : ℕ)^4891*50000000000000^3867 ≤ 21948725765289^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215544967 10000000000 21948725765289 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384620793/10000000000 : ℝ), (-417532549/2500000000 : ℝ), (5215544967/10000000000 : ℝ)] ![(45705000866503/100000000000000 : ℝ), (2599386896939/25000000000000 : ℝ), (21948725765289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384620793/10000000000 : ℝ)|^4891 ≤ (45705000866503/100000000000000 : ℝ)^3867
        have hw : |(5384620793/10000000000 : ℝ)|=(5384620793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-417532549/2500000000 : ℝ)|^4891 ≤ (2599386896939/25000000000000 : ℝ)^3867
        have hw : |(-417532549/2500000000 : ℝ)|=(417532549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215544967/10000000000 : ℝ)|^4891 ≤ (21948725765289/50000000000000 : ℝ)^3867
        have hw : |(5215544967/10000000000 : ℝ)|=(5215544967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_6 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5384620809/10000000000 : ℝ)*x 0 + (5215545111/10000000000 : ℝ)*x 1 + (-83506499/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5384620809/10000000000 : ℝ)^4891 ≤ (1828200041531/4000000000000 : ℝ)^3867 := by
    have hnat : (5384620809 : ℕ)^4891*4000000000000^3867 ≤ 1828200041531^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384620809 10000000000 1828200041531 4000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215545111/10000000000 : ℝ)^4891 ≤ (43897453063519/100000000000000 : ℝ)^3867 := by
    have hnat : (5215545111 : ℕ)^4891*100000000000000^3867 ≤ 43897453063519^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215545111 10000000000 43897453063519 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83506499/500000000 : ℝ)^4891 ≤ (5198772943469/50000000000000 : ℝ)^3867 := by
    have hnat : (83506499 : ℕ)^4891*50000000000000^3867 ≤ 5198772943469^3867*500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83506499 500000000 5198772943469 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5384620809/10000000000 : ℝ), (5215545111/10000000000 : ℝ), (-83506499/500000000 : ℝ)] ![(1828200041531/4000000000000 : ℝ), (43897453063519/100000000000000 : ℝ), (5198772943469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5384620809/10000000000 : ℝ)|^4891 ≤ (1828200041531/4000000000000 : ℝ)^3867
        have hw : |(5384620809/10000000000 : ℝ)|=(5384620809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215545111/10000000000 : ℝ)|^4891 ≤ (43897453063519/100000000000000 : ℝ)^3867
        have hw : |(5215545111/10000000000 : ℝ)|=(5215545111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-83506499/500000000 : ℝ)|^4891 ≤ (5198772943469/50000000000000 : ℝ)^3867
        have hw : |(-83506499/500000000 : ℝ)|=(83506499/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_7 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3902468869/10000000000 : ℝ)*x 0 + (542474763/1250000000 : ℝ)*x 1 + (2169899113/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3902468869/10000000000 : ℝ)^4891 ≤ (15208773522171/50000000000000 : ℝ)^3867 := by
    have hnat : (3902468869 : ℕ)^4891*50000000000000^3867 ≤ 15208773522171^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3902468869 10000000000 15208773522171 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542474763/1250000000 : ℝ)^4891 ≤ (34791225851267/100000000000000 : ℝ)^3867 := by
    have hnat : (542474763 : ℕ)^4891*100000000000000^3867 ≤ 34791225851267^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542474763 1250000000 34791225851267 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2169899113/5000000000 : ℝ)^4891 ≤ (34791227088307/100000000000000 : ℝ)^3867 := by
    have hnat : (2169899113 : ℕ)^4891*100000000000000^3867 ≤ 34791227088307^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169899113 5000000000 34791227088307 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3902468869/10000000000 : ℝ), (542474763/1250000000 : ℝ), (2169899113/5000000000 : ℝ)] ![(15208773522171/50000000000000 : ℝ), (34791225851267/100000000000000 : ℝ), (34791227088307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3902468869/10000000000 : ℝ)|^4891 ≤ (15208773522171/50000000000000 : ℝ)^3867
        have hw : |(3902468869/10000000000 : ℝ)|=(3902468869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542474763/1250000000 : ℝ)|^4891 ≤ (34791225851267/100000000000000 : ℝ)^3867
        have hw : |(542474763/1250000000 : ℝ)|=(542474763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2169899113/5000000000 : ℝ)|^4891 ≤ (34791227088307/100000000000000 : ℝ)^3867
        have hw : |(2169899113/5000000000 : ℝ)|=(2169899113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_8 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-356484561/2000000000 : ℝ)*x 0 + (2538003979/5000000000 : ℝ)*x 1 + (1359833597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (356484561/2000000000 : ℝ)^4891 ≤ (11289502589677/100000000000000 : ℝ)^3867 := by
    have hnat : (356484561 : ℕ)^4891*100000000000000^3867 ≤ 11289502589677^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      356484561 2000000000 11289502589677 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2538003979/5000000000 : ℝ)^4891 ≤ (42417317174563/100000000000000 : ℝ)^3867 := by
    have hnat : (2538003979 : ℕ)^4891*100000000000000^3867 ≤ 42417317174563^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2538003979 5000000000 42417317174563 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359833597/2500000000 : ℝ)^4891 ≤ (9258636045003/20000000000000 : ℝ)^3867 := by
    have hnat : (1359833597 : ℕ)^4891*20000000000000^3867 ≤ 9258636045003^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359833597 2500000000 9258636045003 20000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-356484561/2000000000 : ℝ), (2538003979/5000000000 : ℝ), (1359833597/2500000000 : ℝ)] ![(11289502589677/100000000000000 : ℝ), (42417317174563/100000000000000 : ℝ), (9258636045003/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-356484561/2000000000 : ℝ)|^4891 ≤ (11289502589677/100000000000000 : ℝ)^3867
        have hw : |(-356484561/2000000000 : ℝ)|=(356484561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2538003979/5000000000 : ℝ)|^4891 ≤ (42417317174563/100000000000000 : ℝ)^3867
        have hw : |(2538003979/5000000000 : ℝ)|=(2538003979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359833597/2500000000 : ℝ)|^4891 ≤ (9258636045003/20000000000000 : ℝ)^3867
        have hw : |(1359833597/2500000000 : ℝ)|=(1359833597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_9 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615435783/5000000000 : ℝ)*x 0 + (-196744991/1250000000 : ℝ)*x 1 + (33995841/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615435783/5000000000 : ℝ)^4891 ≤ (2753792072793/6250000000000 : ℝ)^3867 := by
    have hnat : (2615435783 : ℕ)^4891*6250000000000^3867 ≤ 2753792072793^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615435783 5000000000 2753792072793 6250000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196744991/1250000000 : ℝ)^4891 ≤ (4823072374347/50000000000000 : ℝ)^3867 := by
    have hnat : (196744991 : ℕ)^4891*50000000000000^3867 ≤ 4823072374347^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196744991 1250000000 4823072374347 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33995841/62500000 : ℝ)^4891 ≤ (46293182076513/100000000000000 : ℝ)^3867 := by
    have hnat : (33995841 : ℕ)^4891*100000000000000^3867 ≤ 46293182076513^3867*62500000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33995841 62500000 46293182076513 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615435783/5000000000 : ℝ), (-196744991/1250000000 : ℝ), (33995841/62500000 : ℝ)] ![(2753792072793/6250000000000 : ℝ), (4823072374347/50000000000000 : ℝ), (46293182076513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615435783/5000000000 : ℝ)|^4891 ≤ (2753792072793/6250000000000 : ℝ)^3867
        have hw : |(2615435783/5000000000 : ℝ)|=(2615435783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196744991/1250000000 : ℝ)|^4891 ≤ (4823072374347/50000000000000 : ℝ)^3867
        have hw : |(-196744991/1250000000 : ℝ)|=(196744991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33995841/62500000 : ℝ)|^4891 ≤ (46293182076513/100000000000000 : ℝ)^3867
        have hw : |(33995841/62500000 : ℝ)|=(33995841/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_10 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230871617/10000000000 : ℝ)*x 0 + (5439334453/10000000000 : ℝ)*x 1 + (-314792001/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230871617/10000000000 : ℝ)^4891 ≤ (22030336854013/50000000000000 : ℝ)^3867 := by
    have hnat : (5230871617 : ℕ)^4891*50000000000000^3867 ≤ 22030336854013^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230871617 10000000000 22030336854013 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439334453/10000000000 : ℝ)^4891 ≤ (46293180924709/100000000000000 : ℝ)^3867 := by
    have hnat : (5439334453 : ℕ)^4891*100000000000000^3867 ≤ 46293180924709^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439334453 10000000000 46293180924709 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314792001/2000000000 : ℝ)^4891 ≤ (9646145345557/100000000000000 : ℝ)^3867 := by
    have hnat : (314792001 : ℕ)^4891*100000000000000^3867 ≤ 9646145345557^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314792001 2000000000 9646145345557 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230871617/10000000000 : ℝ), (5439334453/10000000000 : ℝ), (-314792001/2000000000 : ℝ)] ![(22030336854013/50000000000000 : ℝ), (46293180924709/100000000000000 : ℝ), (9646145345557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230871617/10000000000 : ℝ)|^4891 ≤ (22030336854013/50000000000000 : ℝ)^3867
        have hw : |(5230871617/10000000000 : ℝ)|=(5230871617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439334453/10000000000 : ℝ)|^4891 ≤ (46293180924709/100000000000000 : ℝ)^3867
        have hw : |(5439334453/10000000000 : ℝ)|=(5439334453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-314792001/2000000000 : ℝ)|^4891 ≤ (9646145345557/100000000000000 : ℝ)^3867
        have hw : |(-314792001/2000000000 : ℝ)|=(314792001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_11 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4546357919/10000000000 : ℝ)*x 0 + (2008481783/5000000000 : ℝ)*x 1 + (803392687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4546357919/10000000000 : ℝ)^4891 ≤ (4612340221091/12500000000000 : ℝ)^3867 := by
    have hnat : (4546357919 : ℕ)^4891*12500000000000^3867 ≤ 4612340221091^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546357919 10000000000 4612340221091 12500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008481783/5000000000 : ℝ)^4891 ≤ (3943829969677/12500000000000 : ℝ)^3867 := by
    have hnat : (2008481783 : ℕ)^4891*12500000000000^3867 ≤ 3943829969677^3867*5000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008481783 5000000000 3943829969677 12500000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803392687/2000000000 : ℝ)^4891 ≤ (31550638456033/100000000000000 : ℝ)^3867 := by
    have hnat : (803392687 : ℕ)^4891*100000000000000^3867 ≤ 31550638456033^3867*2000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803392687 2000000000 31550638456033 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4546357919/10000000000 : ℝ), (2008481783/5000000000 : ℝ), (803392687/2000000000 : ℝ)] ![(4612340221091/12500000000000 : ℝ), (3943829969677/12500000000000 : ℝ), (31550638456033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4546357919/10000000000 : ℝ)|^4891 ≤ (4612340221091/12500000000000 : ℝ)^3867
        have hw : |(4546357919/10000000000 : ℝ)|=(4546357919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008481783/5000000000 : ℝ)|^4891 ≤ (3943829969677/12500000000000 : ℝ)^3867
        have hw : |(2008481783/5000000000 : ℝ)|=(2008481783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803392687/2000000000 : ℝ)|^4891 ≤ (31550638456033/100000000000000 : ℝ)^3867
        have hw : |(803392687/2000000000 : ℝ)|=(803392687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_12 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-288239/1953125 : ℝ)*x 0 + (1385985259/2500000000 : ℝ)*x 1 + (519571001/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (288239/1953125 : ℝ)^4891 ≤ (8891519008431/100000000000000 : ℝ)^3867 := by
    have hnat : (288239 : ℕ)^4891*100000000000000^3867 ≤ 8891519008431^3867*1953125^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288239 1953125 8891519008431 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1385985259/2500000000 : ℝ)^4891 ≤ (47422074621303/100000000000000 : ℝ)^3867 := by
    have hnat : (1385985259 : ℕ)^4891*100000000000000^3867 ≤ 47422074621303^3867*2500000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385985259 2500000000 47422074621303 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519571001/1000000000 : ℝ)^4891 ≤ (43686406355729/100000000000000 : ℝ)^3867 := by
    have hnat : (519571001 : ℕ)^4891*100000000000000^3867 ≤ 43686406355729^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519571001 1000000000 43686406355729 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-288239/1953125 : ℝ), (1385985259/2500000000 : ℝ), (519571001/1000000000 : ℝ)] ![(8891519008431/100000000000000 : ℝ), (47422074621303/100000000000000 : ℝ), (43686406355729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-288239/1953125 : ℝ)|^4891 ≤ (8891519008431/100000000000000 : ℝ)^3867
        have hw : |(-288239/1953125 : ℝ)|=(288239/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1385985259/2500000000 : ℝ)|^4891 ≤ (47422074621303/100000000000000 : ℝ)^3867
        have hw : |(1385985259/2500000000 : ℝ)|=(1385985259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519571001/1000000000 : ℝ)|^4891 ≤ (43686406355729/100000000000000 : ℝ)^3867
        have hw : |(519571001/1000000000 : ℝ)|=(519571001/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_13 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5398256053/10000000000 : ℝ)*x 0 + (-167832881/1000000000 : ℝ)*x 1 + (649463897/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398256053/10000000000 : ℝ)^4891 ≤ (45851434556499/100000000000000 : ℝ)^3867 := by
    have hnat : (5398256053 : ℕ)^4891*100000000000000^3867 ≤ 45851434556499^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398256053 10000000000 45851434556499 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167832881/1000000000 : ℝ)^4891 ≤ (5231073336067/50000000000000 : ℝ)^3867 := by
    have hnat : (167832881 : ℕ)^4891*50000000000000^3867 ≤ 5231073336067^3867*1000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167832881 1000000000 5231073336067 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (649463897/1250000000 : ℝ)^4891 ≤ (2184320937789/5000000000000 : ℝ)^3867 := by
    have hnat : (649463897 : ℕ)^4891*5000000000000^3867 ≤ 2184320937789^3867*1250000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649463897 1250000000 2184320937789 5000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398256053/10000000000 : ℝ), (-167832881/1000000000 : ℝ), (649463897/1250000000 : ℝ)] ![(45851434556499/100000000000000 : ℝ), (5231073336067/50000000000000 : ℝ), (2184320937789/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398256053/10000000000 : ℝ)|^4891 ≤ (45851434556499/100000000000000 : ℝ)^3867
        have hw : |(5398256053/10000000000 : ℝ)|=(5398256053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-167832881/1000000000 : ℝ)|^4891 ≤ (5231073336067/50000000000000 : ℝ)^3867
        have hw : |(-167832881/1000000000 : ℝ)|=(167832881/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(649463897/1250000000 : ℝ)|^4891 ≤ (2184320937789/5000000000000 : ℝ)^3867
        have hw : |(649463897/1250000000 : ℝ)|=(649463897/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_14 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5398254721/10000000000 : ℝ)*x 0 + (5195712389/10000000000 : ℝ)*x 1 + (-1678328989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5398254721/10000000000 : ℝ)^4891 ≤ (4585142024691/10000000000000 : ℝ)^3867 := by
    have hnat : (5398254721 : ℕ)^4891*10000000000000^3867 ≤ 4585142024691^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5398254721 10000000000 4585142024691 10000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195712389/10000000000 : ℝ)^4891 ≤ (21843215827831/50000000000000 : ℝ)^3867 := by
    have hnat : (5195712389 : ℕ)^4891*50000000000000^3867 ≤ 21843215827831^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195712389 10000000000 21843215827831 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1678328989/10000000000 : ℝ)^4891 ≤ (10462148083437/100000000000000 : ℝ)^3867 := by
    have hnat : (1678328989 : ℕ)^4891*100000000000000^3867 ≤ 10462148083437^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678328989 10000000000 10462148083437 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5398254721/10000000000 : ℝ), (5195712389/10000000000 : ℝ), (-1678328989/10000000000 : ℝ)] ![(4585142024691/10000000000000 : ℝ), (21843215827831/50000000000000 : ℝ), (10462148083437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5398254721/10000000000 : ℝ)|^4891 ≤ (4585142024691/10000000000000 : ℝ)^3867
        have hw : |(5398254721/10000000000 : ℝ)|=(5398254721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195712389/10000000000 : ℝ)|^4891 ≤ (21843215827831/50000000000000 : ℝ)^3867
        have hw : |(5195712389/10000000000 : ℝ)|=(5195712389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1678328989/10000000000 : ℝ)|^4891 ≤ (10462148083437/100000000000000 : ℝ)^3867
        have hw : |(-1678328989/10000000000 : ℝ)|=(1678328989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1643_box_15 (p : ℝ) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3843563163/10000000000 : ℝ)*x 0 + (4368352967/10000000000 : ℝ)*x 1 + (4368350749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3843563163/10000000000 : ℝ)^4891 ≤ (29837993543033/100000000000000 : ℝ)^3867 := by
    have hnat : (3843563163 : ℕ)^4891*100000000000000^3867 ≤ 29837993543033^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843563163 10000000000 29837993543033 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4368352967/10000000000 : ℝ)^4891 ≤ (35081014488013/100000000000000 : ℝ)^3867 := by
    have hnat : (4368352967 : ℕ)^4891*100000000000000^3867 ≤ 35081014488013^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368352967 10000000000 35081014488013 100000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4368350749/10000000000 : ℝ)^4891 ≤ (17540495979571/50000000000000 : ℝ)^3867 := by
    have hnat : (4368350749 : ℕ)^4891*50000000000000^3867 ≤ 17540495979571^3867*10000000000^4891 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368350749 10000000000 17540495979571 50000000000000 4891 3867 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4891/1024 : ℝ)) 4891 3867 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3843563163/10000000000 : ℝ), (4368352967/10000000000 : ℝ), (4368350749/10000000000 : ℝ)] ![(29837993543033/100000000000000 : ℝ), (35081014488013/100000000000000 : ℝ), (17540495979571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3843563163/10000000000 : ℝ)|^4891 ≤ (29837993543033/100000000000000 : ℝ)^3867
        have hw : |(3843563163/10000000000 : ℝ)|=(3843563163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4368352967/10000000000 : ℝ)|^4891 ≤ (35081014488013/100000000000000 : ℝ)^3867
        have hw : |(4368352967/10000000000 : ℝ)|=(4368352967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4368350749/10000000000 : ℝ)|^4891 ≤ (17540495979571/50000000000000 : ℝ)^3867
        have hw : |(4368350749/10000000000 : ℝ)|=(4368350749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1643_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(65039/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1171/2000 : ℝ) ∧ (20267/25000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17631/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16281/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10633/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16281/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10633/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16281/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10633/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16281/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10633/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16281/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10633/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16281/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10633/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10633/100000 : ℝ) ^ (4887/1024 : ℝ) ≤ (1131678062813723/50000000000000000000 : ℝ) := by
    have hpowers : (10633/100000 : ℝ)^4887 ≤ (1131678062813723/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10633 : ℕ)^4887*50000000000000000000^1024 ≤ 1131678062813723^1024*100000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10633 100000 1131678062813723 50000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10633/100000 : ℝ)) (X := (1131678062813723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16281/100000 : ℝ) ^ (4887/1024 : ℝ) ≤ (17289352557359601/100000000000000000000 : ℝ) := by
    have hpowers : (16281/100000 : ℝ)^4887 ≤ (17289352557359601/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16281 : ℕ)^4887*100000000000000000000^1024 ≤ 17289352557359601^1024*100000^4887 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16281 100000 17289352557359601 100000000000000000000 4887 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16281/100000 : ℝ)) (X := (17289352557359601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001131678062813723/25000000000000000000 : ℝ) ≤ (2500023712248907/2500000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (25001131678062813723/25000000000000000000 : ℝ)^1024 ≤ (2500023712248907/2500000000000000 : ℝ)^4887 := by
      have hnat : (25001131678062813723 : ℕ)^1024*2500000000000000^4887 ≤ 2500023712248907^4887*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001131678062813723 25000000000000000000 2500023712248907 2500000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500023712248907/2500000000000000 : ℝ)) (X := (25001131678062813723/25000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100019552708682987047/100000000000000000000 : ℝ) ≤ (10000409667006377/10000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (100019552708682987047/100000000000000000000 : ℝ)^1024 ≤ (10000409667006377/10000000000000000 : ℝ)^4887 := by
      have hnat : (100019552708682987047 : ℕ)^1024*10000000000000000^4887 ≤ 10000409667006377^4887*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100019552708682987047 100000000000000000000 10000409667006377 10000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000409667006377/10000000000000000 : ℝ)) (X := (100019552708682987047/100000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50017289352557359601/50000000000000000000 : ℝ) ≤ (5000362242508563/5000000000000000 : ℝ) ^ (4887/1024 : ℝ) := by
    have hpowers : (50017289352557359601/50000000000000000000 : ℝ)^1024 ≤ (5000362242508563/5000000000000000 : ℝ)^4887 := by
      have hnat : (50017289352557359601 : ℕ)^1024*5000000000000000^4887 ≤ 5000362242508563^4887*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017289352557359601 50000000000000000000 5000362242508563 5000000000000000 1024 4887 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000362242508563/5000000000000000 : ℝ)) (X := (50017289352557359601/50000000000000000000 : ℝ)) (by norm_num) 4887 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1131678062813723/50000000000000000000 : ℝ) ≤ ((5647384078731071871/5648000000000000000 : ℝ)+2*(314818010749/564800000000000 : ℝ)*(10633/100000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (5647384078731071871/5648000000000000000 : ℝ)+2*(314818010749/564800000000000 : ℝ)*(10633/100000 : ℝ)=(2500023712248907/2500000000000000 : ℝ) by norm_num, show 1+2*(1131678062813723/50000000000000000000 : ℝ)=(25001131678062813723/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17289352557359601/100000000000000000000 : ℝ)+(1131678062813723/50000000000000000000 : ℝ) ≤ ((5647384078731071871/5648000000000000000 : ℝ)+(314818010749/564800000000000 : ℝ)*((16281/100000 : ℝ)+(10633/100000 : ℝ)))^(4887/1024 : ℝ) := by
    rw [show (5647384078731071871/5648000000000000000 : ℝ)+(314818010749/564800000000000 : ℝ)*((16281/100000 : ℝ)+(10633/100000 : ℝ))=(10000409667006377/10000000000000000 : ℝ) by norm_num, show 1+(17289352557359601/100000000000000000000 : ℝ)+(1131678062813723/50000000000000000000 : ℝ)=(100019552708682987047/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17289352557359601/100000000000000000000 : ℝ) ≤ ((5647384078731071871/5648000000000000000 : ℝ)+2*(314818010749/564800000000000 : ℝ)*(16281/100000 : ℝ))^(4887/1024 : ℝ) := by
    rw [show (5647384078731071871/5648000000000000000 : ℝ)+2*(314818010749/564800000000000 : ℝ)*(16281/100000 : ℝ)=(5000362242508563/5000000000000000 : ℝ) by norm_num, show 1+2*(17289352557359601/100000000000000000000 : ℝ)=(50017289352557359601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5647384078731071871/5648000000000000000 : ℝ)*(X 1 0+X 2 0)+(314818010749/564800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (10633/100000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (5647384078731071871/5648000000000000000 : ℝ)) (alpha := (314818010749/564800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5647384078731071871/5648000000000000000 : ℝ)*(X 0 1+X 2 1)+(314818010749/564800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (10633/100000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (5647384078731071871/5648000000000000000 : ℝ)) (alpha := (314818010749/564800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5647384078731071871/5648000000000000000 : ℝ)*(X 0 2+X 1 2)+(314818010749/564800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4887/1024 : ℝ)) (lo := (10633/100000 : ℝ)) (hi := (16281/100000 : ℝ)) (c := (5647384078731071871/5648000000000000000 : ℝ)) (alpha := (314818010749/564800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-682054291/5000000000 : ℝ)*X 0 0+(676223979/1250000000 : ℝ)*X 0 1+(5409792071/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1312791991/2500000000 : ℝ)*X 1 0+(-1587032177/10000000000 : ℝ)*X 1 1+(5409791957/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1312792057/2500000000 : ℝ)*X 2 0+(1352447899/2500000000 : ℝ)*X 2 1+(-793516157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1115856337/2500000000 : ℝ)*X 0 0+(4059647821/10000000000 : ℝ)*X 0 1+(31715999/78125000 : ℝ)*X 0 2+(1115856337/2500000000 : ℝ)*X 1 0+(4059647821/10000000000 : ℝ)*X 1 1+(31715999/78125000 : ℝ)*X 1 2+(1115856337/2500000000 : ℝ)*X 2 0+(4059647821/10000000000 : ℝ)*X 2 1+(31715999/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-473943769/2500000000 : ℝ)*X 0 0+(1303886211/2500000000 : ℝ)*X 0 1+(260777243/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5384620793/10000000000 : ℝ)*X 1 0+(-417532549/2500000000 : ℝ)*X 1 1+(5215544967/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5384620809/10000000000 : ℝ)*X 2 0+(5215545111/10000000000 : ℝ)*X 2 1+(-83506499/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3902468869/10000000000 : ℝ)*X 0 0+(542474763/1250000000 : ℝ)*X 0 1+(2169899113/5000000000 : ℝ)*X 0 2+(3902468869/10000000000 : ℝ)*X 1 0+(542474763/1250000000 : ℝ)*X 1 1+(2169899113/5000000000 : ℝ)*X 1 2+(3902468869/10000000000 : ℝ)*X 2 0+(542474763/1250000000 : ℝ)*X 2 1+(2169899113/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-356484561/2000000000 : ℝ)*X 0 0+(2538003979/5000000000 : ℝ)*X 0 1+(1359833597/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615435783/5000000000 : ℝ)*X 1 0+(-196744991/1250000000 : ℝ)*X 1 1+(33995841/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230871617/10000000000 : ℝ)*X 2 0+(5439334453/10000000000 : ℝ)*X 2 1+(-314792001/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4546357919/10000000000 : ℝ)*X 0 0+(2008481783/5000000000 : ℝ)*X 0 1+(803392687/2000000000 : ℝ)*X 0 2+(4546357919/10000000000 : ℝ)*X 1 0+(2008481783/5000000000 : ℝ)*X 1 1+(803392687/2000000000 : ℝ)*X 1 2+(4546357919/10000000000 : ℝ)*X 2 0+(2008481783/5000000000 : ℝ)*X 2 1+(803392687/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-288239/1953125 : ℝ)*X 0 0+(1385985259/2500000000 : ℝ)*X 0 1+(519571001/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5398256053/10000000000 : ℝ)*X 1 0+(-167832881/1000000000 : ℝ)*X 1 1+(649463897/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5398254721/10000000000 : ℝ)*X 2 0+(5195712389/10000000000 : ℝ)*X 2 1+(-1678328989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3843563163/10000000000 : ℝ)*X 0 0+(4368352967/10000000000 : ℝ)*X 0 1+(4368350749/10000000000 : ℝ)*X 0 2+(3843563163/10000000000 : ℝ)*X 1 0+(4368352967/10000000000 : ℝ)*X 1 1+(4368350749/10000000000 : ℝ)*X 1 2+(3843563163/10000000000 : ℝ)*X 2 0+(4368352967/10000000000 : ℝ)*X 2 1+(4368350749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1643_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-65039/100000 : ℝ) ≤ (-18366267614281008337830951057/28240000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1072051/12500000000000 : ℝ)*(upper0) + (22588203/100000000000000 : ℝ)*(lower1) + (9293817/20000000000000 : ℝ)*(lower2) + (2499651/25000000000000 : ℝ)*(lower3) + (1745604192432329/100000000000000 : ℝ)*(major0) + (1745604192432329/100000000000000 : ℝ)*(major1) + (1745604192432329/100000000000000 : ℝ)*(major2) + (149368857/50000000000000 : ℝ)*(sp3) + (50668694746617/2000000000000 : ℝ)*(sp4) + (1266713708711389/50000000000000 : ℝ)*(sp5) + (158337269146271/6250000000000 : ℝ)*(sp6) + (979452134931927/100000000000000 : ℝ)*(sp7) + (7319908073/100000000000000 : ℝ)*(sp13) + (19215495257/50000000000000 : ℝ)*(sp14) + (979452433669641/100000000000000 : ℝ)*(f.failure) + (50668694746617/2000000000000 : ℝ)*(f.sum) + (84041785579979/28240000000000000000000000000 : ℝ)*base66 + (1667173778717527559/564800000000000000000000000000000 : ℝ)*base67 + (2920514620119127559/564800000000000000000000000000000 : ℝ)*base69 + (1702857271151272441/564800000000000000000000000000000 : ℝ)*base72 + (76243014443739/28240000000000000000000000000 : ℝ)*base74 + (45166122956072441/564800000000000000000000000000000 : ℝ)*base76 + (2023732893592727559/564800000000000000000000000000000 : ℝ)*base77 + (489536394444072441/564800000000000000000000000000000 : ℝ)*base80 + (83772662156261/28240000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (45327937/10000000000000000000000 : ℝ)*base89 + (45327937/10000000000000000000000 : ℝ)*base91 + (45327937/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1171/2000 : ℝ) ≤ (82676558053546790877938496583569/141200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48854327/100000000000000 : ℝ)*(lower0) + (46251779/100000000000000 : ℝ)*(lower1) + (45622847/100000000000000 : ℝ)*(lower3) + (7277903/25000000000000 : ℝ)*(lower5) + (917511951006213/50000000000000 : ℝ)*(major0) + (917511951006213/50000000000000 : ℝ)*(major1) + (917511951006213/50000000000000 : ℝ)*(major2) + (2620903256618269/100000000000000 : ℝ)*(sp0) + (2620904681644029/100000000000000 : ℝ)*(sp1) + (655217647820247/25000000000000 : ℝ)*(sp2) + (205924685521807/20000000000000 : ℝ)*(sp3) + (2093720427/100000000000000 : ℝ)*(sp7) + (213064769/625000000000 : ℝ)*(sp10) + (8906411/625000000000 : ℝ)*(sp12) + (514812760664731/50000000000000 : ℝ)*(f.failure) + (2620904681644029/100000000000000 : ℝ)*(f.sum) + (13702704407337/14120000000000000000000000000 : ℝ)*base65 + (862958701120495477/282400000000000000000000000000000 : ℝ)*base68 + (839516510504495477/282400000000000000000000000000000 : ℝ)*base70 + (993849375091695477/282400000000000000000000000000000 : ℝ)*base72 + (57274382202337/14120000000000000000000000000 : ℝ)*base73 + (266660218554095477/282400000000000000000000000000000 : ℝ)*base76 + (917660313097104523/282400000000000000000000000000000 : ℝ)*base77 + (2326035448159504523/282400000000000000000000000000000 : ℝ)*base79 + (56924028572737/14120000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (12064067/5000000000000000000000 : ℝ)*base89 + (12064067/5000000000000000000000 : ℝ)*base91 + (12064067/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (20267/25000 : ℝ) ≤ (11447170495312973952392914329/14120000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1077691/50000000000000 : ℝ)*(upper1) + (434813/100000000000000 : ℝ)*(upper2) + (18471941/100000000000000 : ℝ)*(upper3) + (680349/12500000000000 : ℝ)*(lower5) + (965794225025607/50000000000000 : ℝ)*(major0) + (965794225025607/50000000000000 : ℝ)*(major1) + (965794225025607/50000000000000 : ℝ)*(major2) + (305150067/100000000000000 : ℝ)*(sp0) + (10806519901/100000000000000 : ℝ)*(sp1) + (3676262387/100000000000000 : ℝ)*(sp2) + (275234550445997/10000000000000 : ℝ)*(sp8) + (344041875386267/12500000000000 : ℝ)*(sp9) + (55046842666953/2000000000000 : ℝ)*(sp10) + (541903776484019/50000000000000 : ℝ)*(sp11) + (541903776484019/50000000000000 : ℝ)*(f.failure) + (688086452402509/25000000000000 : ℝ)*(f.sum) + (23710903091717/14120000000000000000000000000 : ℝ)*base66 + (2155459216640030697/282400000000000000000000000000000 : ℝ)*base67 + (778976165483969303/282400000000000000000000000000000 : ℝ)*base70 + (671808702760030697/282400000000000000000000000000000 : ℝ)*base71 + (79229873268883/14120000000000000000000000000 : ℝ)*base73 + (1348850695803969303/282400000000000000000000000000000 : ℝ)*base76 + (736623383910369303/282400000000000000000000000000000 : ℝ)*base78 + (305233410564830697/282400000000000000000000000000000 : ℝ)*base79 + (122722837869797/14120000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (12585317/5000000000000000000000 : ℝ)*base90 + (12585317/5000000000000000000000 : ℝ)*base92 + (12585317/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-17631/20000 : ℝ) ≤ (-15558944063649407349485599995447/17650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (580166799/100000000000000 : ℝ)*(upper3) + (1039189/3125000000000 : ℝ)*(lower4) + (3648009/5000000000000 : ℝ)*(upper5) + (246915964012619/12500000000000 : ℝ)*(major0) + (246915964012619/12500000000000 : ℝ)*(major1) + (246915964012619/12500000000000 : ℝ)*(major2) + (314825933/20000000000000 : ℝ)*(sp4) + (128070560929/50000000000000 : ℝ)*(sp5) + (122961742681/100000000000000 : ℝ)*(sp7) + (2663680039/25000000000000 : ℝ)*(sp8) + (179479869622227/6250000000000 : ℝ)*(sp12) + (574286800336719/20000000000000 : ℝ)*(sp13) + (1435845071402727/50000000000000 : ℝ)*(sp14) + (1108226538848567/100000000000000 : ℝ)*(sp15) + (69271843786953/6250000000000 : ℝ)*(f.failure) + (1435845071402727/50000000000000 : ℝ)*(f.sum) + (10667910616731/3530000000000000000000000000 : ℝ)*base65 + (631120449202450149/70600000000000000000000000000000 : ℝ)*base67 + (174794188864050149/70600000000000000000000000000000 : ℝ)*base69 + (705282885242850149/70600000000000000000000000000000 : ℝ)*base71 + (15425056289281/3530000000000000000000000000 : ℝ)*base73 + (358857308609250149/70600000000000000000000000000000 : ℝ)*base75 + (111755434249850149/70600000000000000000000000000000 : ℝ)*base77 + (148251034705149851/70600000000000000000000000000000 : ℝ)*base80 + (3828033463641/3530000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1796479/625000000000000000000 : ℝ)*base90 + (1796479/625000000000000000000 : ℝ)*base92 + (1796479/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1643_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65039/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1171/2000 : ℝ) else (20267/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17631/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1643_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1643_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65039/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1171/2000 : ℝ) else (20267/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17631/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1643_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4887/1024 : ℝ) ≤ p) (hpb : p ≤ (4891/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (178222457/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16281/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10633/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(65039/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(1171/2000 : ℝ) else (20267/25000 : ℝ) ≤ X j i ∧ X j i ≤ (17631/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1643_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
