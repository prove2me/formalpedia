-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1304_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:37:23.415089+00:00
-- url     : https://prove2.me/submissions/6511708a-4a69-4c5f-bcce-86ff0f9c6cb8

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
theorem support_rectangle_w1304_s3_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1037532653/5000000000 : ℝ)*x 0 + (5432317663/10000000000 : ℝ)*x 1 + (5227153309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1037532653/5000000000 : ℝ)^533 ≤ (6311754318883/50000000000000 : ℝ)^405 := by
    have hnat : (1037532653 : ℕ)^533*50000000000000^405 ≤ 6311754318883^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037532653 5000000000 6311754318883 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5432317663/10000000000 : ℝ)^533 ≤ (4479477719899/10000000000000 : ℝ)^405 := by
    have hnat : (5432317663 : ℕ)^533*10000000000000^405 ≤ 4479477719899^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5432317663 10000000000 4479477719899 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227153309/10000000000 : ℝ)^533 ≤ (851634282961/2000000000000 : ℝ)^405 := by
    have hnat : (5227153309 : ℕ)^533*2000000000000^405 ≤ 851634282961^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227153309 10000000000 851634282961 2000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1037532653/5000000000 : ℝ), (5432317663/10000000000 : ℝ), (5227153309/10000000000 : ℝ)] ![(6311754318883/50000000000000 : ℝ), (4479477719899/10000000000000 : ℝ), (851634282961/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1037532653/5000000000 : ℝ)|^533 ≤ (6311754318883/50000000000000 : ℝ)^405
        have hw : |(-1037532653/5000000000 : ℝ)|=(1037532653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5432317663/10000000000 : ℝ)|^533 ≤ (4479477719899/10000000000000 : ℝ)^405
        have hw : |(5432317663/10000000000 : ℝ)|=(5432317663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227153309/10000000000 : ℝ)|^533 ≤ (851634282961/2000000000000 : ℝ)^405
        have hw : |(5227153309/10000000000 : ℝ)|=(5227153309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s3_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2677045629/5000000000 : ℝ)*x 0 + (-545006999/2500000000 : ℝ)*x 1 + (5227153471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677045629/5000000000 : ℝ)^533 ≤ (43947793389763/100000000000000 : ℝ)^405 := by
    have hnat : (2677045629 : ℕ)^533*100000000000000^405 ≤ 43947793389763^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677045629 5000000000 43947793389763 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545006999/2500000000 : ℝ)^533 ≤ (13470490710159/100000000000000 : ℝ)^405 := by
    have hnat : (545006999 : ℕ)^533*100000000000000^405 ≤ 13470490710159^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545006999 2500000000 13470490710159 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227153471/10000000000 : ℝ)^533 ≤ (1330678621401/3125000000000 : ℝ)^405 := by
    have hnat : (5227153471 : ℕ)^533*3125000000000^405 ≤ 1330678621401^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227153471 10000000000 1330678621401 3125000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677045629/5000000000 : ℝ), (-545006999/2500000000 : ℝ), (5227153471/10000000000 : ℝ)] ![(43947793389763/100000000000000 : ℝ), (13470490710159/100000000000000 : ℝ), (1330678621401/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677045629/5000000000 : ℝ)|^533 ≤ (43947793389763/100000000000000 : ℝ)^405
        have hw : |(2677045629/5000000000 : ℝ)|=(2677045629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-545006999/2500000000 : ℝ)|^533 ≤ (13470490710159/100000000000000 : ℝ)^405
        have hw : |(-545006999/2500000000 : ℝ)|=(545006999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227153471/10000000000 : ℝ)|^533 ≤ (1330678621401/3125000000000 : ℝ)^405
        have hw : |(5227153471/10000000000 : ℝ)|=(5227153471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s3_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5354091337/10000000000 : ℝ)*x 0 + (32669707/62500000 : ℝ)*x 1 + (-2180028353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354091337/10000000000 : ℝ)^533 ≤ (43947794243159/100000000000000 : ℝ)^405 := by
    have hnat : (5354091337 : ℕ)^533*100000000000000^405 ≤ 43947794243159^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354091337 10000000000 43947794243159 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32669707/62500000 : ℝ)^533 ≤ (21290856060903/50000000000000 : ℝ)^405 := by
    have hnat : (32669707 : ℕ)^533*50000000000000^405 ≤ 21290856060903^405*62500000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32669707 62500000 21290856060903 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180028353/10000000000 : ℝ)^533 ≤ (13470493613257/100000000000000 : ℝ)^405 := by
    have hnat : (2180028353 : ℕ)^533*100000000000000^405 ≤ 13470493613257^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180028353 10000000000 13470493613257 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354091337/10000000000 : ℝ), (32669707/62500000 : ℝ), (-2180028353/10000000000 : ℝ)] ![(43947794243159/100000000000000 : ℝ), (21290856060903/50000000000000 : ℝ), (13470493613257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354091337/10000000000 : ℝ)|^533 ≤ (43947794243159/100000000000000 : ℝ)^405
        have hw : |(5354091337/10000000000 : ℝ)|=(5354091337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32669707/62500000 : ℝ)|^533 ≤ (21290856060903/50000000000000 : ℝ)^405
        have hw : |(32669707/62500000 : ℝ)|=(32669707/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2180028353/10000000000 : ℝ)|^533 ≤ (13470493613257/100000000000000 : ℝ)^405
        have hw : |(-2180028353/10000000000 : ℝ)|=(2180028353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s3_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (541916457/1250000000 : ℝ)*x 0 + (4128448339/10000000000 : ℝ)*x 1 + (4552044439/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541916457/1250000000 : ℝ)^533 ≤ (33289207589471/100000000000000 : ℝ)^405 := by
    have hnat : (541916457 : ℕ)^533*100000000000000^405 ≤ 33289207589471^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541916457 1250000000 33289207589471 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128448339/10000000000 : ℝ)^533 ≤ (15607255184593/50000000000000 : ℝ)^405 := by
    have hnat : (4128448339 : ℕ)^533*50000000000000^405 ≤ 15607255184593^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128448339 10000000000 15607255184593 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4552044439/10000000000 : ℝ)^533 ≤ (35496282029053/100000000000000 : ℝ)^405 := by
    have hnat : (4552044439 : ℕ)^533*100000000000000^405 ≤ 35496282029053^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4552044439 10000000000 35496282029053 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541916457/1250000000 : ℝ), (4128448339/10000000000 : ℝ), (4552044439/10000000000 : ℝ)] ![(33289207589471/100000000000000 : ℝ), (15607255184593/50000000000000 : ℝ), (35496282029053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541916457/1250000000 : ℝ)|^533 ≤ (33289207589471/100000000000000 : ℝ)^405
        have hw : |(541916457/1250000000 : ℝ)|=(541916457/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128448339/10000000000 : ℝ)|^533 ≤ (15607255184593/50000000000000 : ℝ)^405
        have hw : |(4128448339/10000000000 : ℝ)|=(4128448339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4552044439/10000000000 : ℝ)|^533 ≤ (35496282029053/100000000000000 : ℝ)^405
        have hw : |(4552044439/10000000000 : ℝ)|=(4552044439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s3_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-259385879/1250000000 : ℝ)*x 0 + (2614014627/5000000000 : ℝ)*x 1 + (2715718119/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259385879/1250000000 : ℝ)^533 ≤ (12623682578377/100000000000000 : ℝ)^405 := by
    have hnat : (259385879 : ℕ)^533*100000000000000^405 ≤ 12623682578377^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259385879 1250000000 12623682578377 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614014627/5000000000 : ℝ)^533 ≤ (8518221058091/20000000000000 : ℝ)^405 := by
    have hnat : (2614014627 : ℕ)^533*20000000000000^405 ≤ 8518221058091^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614014627 5000000000 8518221058091 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715718119/5000000000 : ℝ)^533 ≤ (22392606059163/50000000000000 : ℝ)^405 := by
    have hnat : (2715718119 : ℕ)^533*50000000000000^405 ≤ 22392606059163^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715718119 5000000000 22392606059163 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259385879/1250000000 : ℝ), (2614014627/5000000000 : ℝ), (2715718119/5000000000 : ℝ)] ![(12623682578377/100000000000000 : ℝ), (8518221058091/20000000000000 : ℝ), (22392606059163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259385879/1250000000 : ℝ)|^533 ≤ (12623682578377/100000000000000 : ℝ)^405
        have hw : |(-259385879/1250000000 : ℝ)|=(259385879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614014627/5000000000 : ℝ)|^533 ≤ (8518221058091/20000000000000 : ℝ)^405
        have hw : |(2614014627/5000000000 : ℝ)|=(2614014627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715718119/5000000000 : ℝ)|^533 ≤ (22392606059163/50000000000000 : ℝ)^405
        have hw : |(2715718119/5000000000 : ℝ)|=(2715718119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s3_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2650740869/5000000000 : ℝ)*x 0 + (-1975745139/10000000000 : ℝ)*x 1 + (5431436203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650740869/5000000000 : ℝ)^533 ≤ (43380364513911/100000000000000 : ℝ)^405 := by
    have hnat : (2650740869 : ℕ)^533*100000000000000^405 ≤ 43380364513911^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650740869 5000000000 43380364513911 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975745139/10000000000 : ℝ)^533 ≤ (5917211860763/50000000000000 : ℝ)^405 := by
    have hnat : (1975745139 : ℕ)^533*50000000000000^405 ≤ 5917211860763^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975745139 10000000000 5917211860763 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5431436203/10000000000 : ℝ)^533 ≤ (22392605869261/50000000000000 : ℝ)^405 := by
    have hnat : (5431436203 : ℕ)^533*50000000000000^405 ≤ 22392605869261^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431436203 10000000000 22392605869261 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650740869/5000000000 : ℝ), (-1975745139/10000000000 : ℝ), (5431436203/10000000000 : ℝ)] ![(43380364513911/100000000000000 : ℝ), (5917211860763/50000000000000 : ℝ), (22392605869261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650740869/5000000000 : ℝ)|^533 ≤ (43380364513911/100000000000000 : ℝ)^405
        have hw : |(2650740869/5000000000 : ℝ)|=(2650740869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1975745139/10000000000 : ℝ)|^533 ≤ (5917211860763/50000000000000 : ℝ)^405
        have hw : |(-1975745139/10000000000 : ℝ)|=(1975745139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5431436203/10000000000 : ℝ)|^533 ≤ (22392605869261/50000000000000 : ℝ)^405
        have hw : |(5431436203/10000000000 : ℝ)|=(5431436203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s3_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1325370461/2500000000 : ℝ)*x 0 + (5431436093/10000000000 : ℝ)*x 1 + (-1975745147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325370461/2500000000 : ℝ)^533 ≤ (21690182827703/50000000000000 : ℝ)^405 := by
    have hnat : (1325370461 : ℕ)^533*50000000000000^405 ≤ 21690182827703^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325370461 2500000000 21690182827703 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5431436093/10000000000 : ℝ)^533 ≤ (895704210897/2000000000000 : ℝ)^405 := by
    have hnat : (5431436093 : ℕ)^533*2000000000000^405 ≤ 895704210897^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5431436093 10000000000 895704210897 2000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1975745147/10000000000 : ℝ)^533 ≤ (1183442378459/10000000000000 : ℝ)^405 := by
    have hnat : (1975745147 : ℕ)^533*10000000000000^405 ≤ 1183442378459^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975745147 10000000000 1183442378459 10000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325370461/2500000000 : ℝ), (5431436093/10000000000 : ℝ), (-1975745147/10000000000 : ℝ)] ![(21690182827703/50000000000000 : ℝ), (895704210897/2000000000000 : ℝ), (1183442378459/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325370461/2500000000 : ℝ)|^533 ≤ (21690182827703/50000000000000 : ℝ)^405
        have hw : |(1325370461/2500000000 : ℝ)|=(1325370461/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5431436093/10000000000 : ℝ)|^533 ≤ (895704210897/2000000000000 : ℝ)^405
        have hw : |(5431436093/10000000000 : ℝ)|=(5431436093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1975745147/10000000000 : ℝ)|^533 ≤ (1183442378459/10000000000000 : ℝ)^405
        have hw : |(-1975745147/10000000000 : ℝ)|=(1975745147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s3_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (270961003/625000000 : ℝ)*x 0 + (4550235701/10000000000 : ℝ)*x 1 + (516283557/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270961003/625000000 : ℝ)^533 ≤ (16644828094457/50000000000000 : ℝ)^405 := by
    have hnat : (270961003 : ℕ)^533*50000000000000^405 ≤ 16644828094457^405*625000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270961003 625000000 16644828094457 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4550235701/10000000000 : ℝ)^533 ≤ (7095544243607/20000000000000 : ℝ)^405 := by
    have hnat : (4550235701 : ℕ)^533*20000000000000^405 ≤ 7095544243607^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550235701 10000000000 7095544243607 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516283557/1250000000 : ℝ)^533 ≤ (1561631128901/5000000000000 : ℝ)^405 := by
    have hnat : (516283557 : ℕ)^533*5000000000000^405 ≤ 1561631128901^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516283557 1250000000 1561631128901 5000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270961003/625000000 : ℝ), (4550235701/10000000000 : ℝ), (516283557/1250000000 : ℝ)] ![(16644828094457/50000000000000 : ℝ), (7095544243607/20000000000000 : ℝ), (1561631128901/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270961003/625000000 : ℝ)|^533 ≤ (16644828094457/50000000000000 : ℝ)^405
        have hw : |(270961003/625000000 : ℝ)|=(270961003/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4550235701/10000000000 : ℝ)|^533 ≤ (7095544243607/20000000000000 : ℝ)^405
        have hw : |(4550235701/10000000000 : ℝ)|=(4550235701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(516283557/1250000000 : ℝ)|^533 ≤ (1561631128901/5000000000000 : ℝ)^405
        have hw : |(516283557/1250000000 : ℝ)|=(516283557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16263/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1071/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15051/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16263/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1199/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16263/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1199/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16263/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1199/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16263/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1199/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16263/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1199/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16263/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1199/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1199/12500 : ℝ) ^ (4263/1024 : ℝ) ≤ (2887821778096369/50000000000000000000 : ℝ) := by
    have hpowers : (1199/12500 : ℝ)^4263 ≤ (2887821778096369/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1199 : ℕ)^4263*50000000000000000000^1024 ≤ 2887821778096369^1024*12500^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1199 12500 2887821778096369 50000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1199/12500 : ℝ)) (X := (2887821778096369/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16263/100000 : ℝ) ^ (4263/1024 : ℝ) ≤ (13004707158121979/25000000000000000000 : ℝ) := by
    have hpowers : (16263/100000 : ℝ)^4263 ≤ (13004707158121979/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16263 : ℕ)^4263*25000000000000000000^1024 ≤ 13004707158121979^1024*100000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16263 100000 13004707158121979 25000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16263/100000 : ℝ)) (X := (13004707158121979/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002887821778096369/25000000000000000000 : ℝ) ≤ (10000277457165559/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (25002887821778096369/25000000000000000000 : ℝ)^1024 ≤ (10000277457165559/10000000000000000 : ℝ)^4263 := by
      have hnat : (25002887821778096369 : ℕ)^1024*10000000000000000^4263 ≤ 10000277457165559^4263*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002887821778096369 25000000000000000000 10000277457165559 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000277457165559/10000000000000000 : ℝ)) (X := (25002887821778096369/25000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50028897236094340327/50000000000000000000 : ℝ) ≤ (625086747229159/625000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50028897236094340327/50000000000000000000 : ℝ)^1024 ≤ (625086747229159/625000000000000 : ℝ)^4263 := by
      have hnat : (50028897236094340327 : ℕ)^1024*625000000000000^4263 ≤ 625086747229159^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028897236094340327 50000000000000000000 625086747229159 625000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625086747229159/625000000000000 : ℝ)) (X := (50028897236094340327/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12513004707158121979/12500000000000000000 : ℝ) ≤ (10002498454167529/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (12513004707158121979/12500000000000000000 : ℝ)^1024 ≤ (10002498454167529/10000000000000000 : ℝ)^4263 := by
      have hnat : (12513004707158121979 : ℕ)^1024*10000000000000000^4263 ≤ 10002498454167529^4263*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12513004707158121979 12500000000000000000 10002498454167529 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002498454167529/10000000000000000 : ℝ)) (X := (12513004707158121979/12500000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2887821778096369/50000000000000000000 : ℝ) ≤ ((66690547113508547849/66710000000000000000 : ℝ)+2*(222099700197/133420000000000 : ℝ)*(1199/12500 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (66690547113508547849/66710000000000000000 : ℝ)+2*(222099700197/133420000000000 : ℝ)*(1199/12500 : ℝ)=(10000277457165559/10000000000000000 : ℝ) by norm_num, show 1+2*(2887821778096369/50000000000000000000 : ℝ)=(25002887821778096369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13004707158121979/25000000000000000000 : ℝ)+(2887821778096369/50000000000000000000 : ℝ) ≤ ((66690547113508547849/66710000000000000000 : ℝ)+(222099700197/133420000000000 : ℝ)*((16263/100000 : ℝ)+(1199/12500 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (66690547113508547849/66710000000000000000 : ℝ)+(222099700197/133420000000000 : ℝ)*((16263/100000 : ℝ)+(1199/12500 : ℝ))=(625086747229159/625000000000000 : ℝ) by norm_num, show 1+(13004707158121979/25000000000000000000 : ℝ)+(2887821778096369/50000000000000000000 : ℝ)=(50028897236094340327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13004707158121979/25000000000000000000 : ℝ) ≤ ((66690547113508547849/66710000000000000000 : ℝ)+2*(222099700197/133420000000000 : ℝ)*(16263/100000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (66690547113508547849/66710000000000000000 : ℝ)+2*(222099700197/133420000000000 : ℝ)*(16263/100000 : ℝ)=(10002498454167529/10000000000000000 : ℝ) by norm_num, show 1+2*(13004707158121979/25000000000000000000 : ℝ)=(12513004707158121979/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66690547113508547849/66710000000000000000 : ℝ)*(X 1 0+X 2 0)+(222099700197/133420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (1199/12500 : ℝ)) (hi := (16263/100000 : ℝ)) (c := (66690547113508547849/66710000000000000000 : ℝ)) (alpha := (222099700197/133420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66690547113508547849/66710000000000000000 : ℝ)*(X 0 1+X 2 1)+(222099700197/133420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (1199/12500 : ℝ)) (hi := (16263/100000 : ℝ)) (c := (66690547113508547849/66710000000000000000 : ℝ)) (alpha := (222099700197/133420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66690547113508547849/66710000000000000000 : ℝ)*(X 0 2+X 1 2)+(222099700197/133420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (1199/12500 : ℝ)) (hi := (16263/100000 : ℝ)) (c := (66690547113508547849/66710000000000000000 : ℝ)) (alpha := (222099700197/133420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1037532653/5000000000 : ℝ)*X 0 0+(5432317663/10000000000 : ℝ)*X 0 1+(5227153309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677045629/5000000000 : ℝ)*X 1 0+(-545006999/2500000000 : ℝ)*X 1 1+(5227153471/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354091337/10000000000 : ℝ)*X 2 0+(32669707/62500000 : ℝ)*X 2 1+(-2180028353/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((541916457/1250000000 : ℝ)*X 0 0+(4128448339/10000000000 : ℝ)*X 0 1+(4552044439/10000000000 : ℝ)*X 0 2+(541916457/1250000000 : ℝ)*X 1 0+(4128448339/10000000000 : ℝ)*X 1 1+(4552044439/10000000000 : ℝ)*X 1 2+(541916457/1250000000 : ℝ)*X 2 0+(4128448339/10000000000 : ℝ)*X 2 1+(4552044439/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-259385879/1250000000 : ℝ)*X 0 0+(2614014627/5000000000 : ℝ)*X 0 1+(2715718119/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650740869/5000000000 : ℝ)*X 1 0+(-1975745139/10000000000 : ℝ)*X 1 1+(5431436203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325370461/2500000000 : ℝ)*X 2 0+(5431436093/10000000000 : ℝ)*X 2 1+(-1975745147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((270961003/625000000 : ℝ)*X 0 0+(4550235701/10000000000 : ℝ)*X 0 1+(516283557/1250000000 : ℝ)*X 0 2+(270961003/625000000 : ℝ)*X 1 0+(4550235701/10000000000 : ℝ)*X 1 1+(516283557/1250000000 : ℝ)*X 1 2+(270961003/625000000 : ℝ)*X 2 0+(4550235701/10000000000 : ℝ)*X 2 1+(516283557/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3062274559967708738347071369/333550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1873164177/100000000000000 : ℝ)*(base19) + (1810688421/100000000000000 : ℝ)*(base23) + (114115589/100000000000000 : ℝ)*(lower2) + (455748437/100000000000000 : ℝ)*(upper3) + (5269913/12500000000000 : ℝ)*(lower4) + (361748827971609/10000000000000 : ℝ)*(major0) + (361748827971609/10000000000000 : ℝ)*(major1) + (361748827971609/10000000000000 : ℝ)*(major2) + (487417857555821/10000000000000 : ℝ)*(sp0) + (2437101011241151/50000000000000 : ℝ)*(sp1) + (4874202084958057/100000000000000 : ℝ)*(sp2) + (590188156517189/25000000000000 : ℝ)*(sp3) + (6330022067/25000000000000 : ℝ)*(sp4) + (9865844201/50000000000000 : ℝ)*(sp7) + (1180386178878579/50000000000000 : ℝ)*(f.failure) + (2437101947823239/50000000000000 : ℝ)*(f.sum) + (10571822528007/3335500000000000000000000000 : ℝ)*base65 + (1852578111658280959/667100000000000000000000000000000 : ℝ)*base68 + (1433490202800480959/667100000000000000000000000000000 : ℝ)*base70 + (2681022757554280959/667100000000000000000000000000000 : ℝ)*base72 + (199750714409/416937500000000000000000000 : ℝ)*base74 + (9997651670413280959/667100000000000000000000000000000 : ℝ)*base76 + (8280751078614580959/667100000000000000000000000000000 : ℝ)*base78 + (1507575697758080959/667100000000000000000000000000000 : ℝ)*base80 + (3782608982881/1334200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (52187487/5000000000000000000000 : ℝ)*base89 + (52187487/5000000000000000000000 : ℝ)*base91 + (52187487/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (26811499857843605021726872947/3335500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1884467783/100000000000000 : ℝ)*(base19) + (1033863871/50000000000000 : ℝ)*(base23) + (197419859/100000000000000 : ℝ)*(upper3) + (7687451/20000000000000 : ℝ)*(lower4) + (102849053/50000000000000 : ℝ)*(upper5) + (3648695280160201/100000000000000 : ℝ)*(major0) + (3648695280160201/100000000000000 : ℝ)*(major1) + (3648695280160201/100000000000000 : ℝ)*(major2) + (3163773957/10000000000000 : ℝ)*(sp1) + (8223328367/25000000000000 : ℝ)*(sp2) + (76816441412353/1562500000000 : ℝ)*(sp4) + (122905468204581/2500000000000 : ℝ)*(sp5) + (2458108644674691/50000000000000 : ℝ)*(sp6) + (297642255248621/12500000000000 : ℝ)*(sp7) + (297642255248621/12500000000000 : ℝ)*(f.failure) + (76816441412353/1562500000000 : ℝ)*(f.sum) + (9516937094323/6671000000000000000000000000 : ℝ)*base66 + (56151579482663542351/6671000000000000000000000000000000 : ℝ)*base68 + (14986448648591542351/6671000000000000000000000000000000 : ℝ)*base70 + (36741395778731542351/6671000000000000000000000000000000 : ℝ)*base72 + (22859197049851/6671000000000000000000000000 : ℝ)*base74 + (35201661961865542351/6671000000000000000000000000000000 : ℝ)*base76 + (29338215107844457649/6671000000000000000000000000000000 : ℝ)*base77 + (1393224889958457649/6671000000000000000000000000000000 : ℝ)*base79 + (20499074379953/6671000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (7094113/1250000000000000000000 : ℝ)*base89 + (7094113/1250000000000000000000 : ℝ)*base91 + (7094113/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1304_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16263/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1071/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15051/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1304_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1304_s4_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-259608049/1250000000 : ℝ)*x 0 + (2709008893/5000000000 : ℝ)*x 1 + (5240273319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259608049/1250000000 : ℝ)^533 ≤ (6318957128111/50000000000000 : ℝ)^405 := by
    have hnat : (259608049 : ℕ)^533*50000000000000^405 ≤ 6318957128111^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259608049 1250000000 6318957128111 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2709008893/5000000000 : ℝ)^533 ≤ (557995723423/1250000000000 : ℝ)^405 := by
    have hnat : (2709008893 : ℕ)^533*1250000000000^405 ≤ 557995723423^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709008893 5000000000 557995723423 1250000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240273319/10000000000 : ℝ)^533 ≤ (267015174043/625000000000 : ℝ)^405 := by
    have hnat : (5240273319 : ℕ)^533*625000000000^405 ≤ 267015174043^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240273319 10000000000 267015174043 625000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259608049/1250000000 : ℝ), (2709008893/5000000000 : ℝ), (5240273319/10000000000 : ℝ)] ![(6318957128111/50000000000000 : ℝ), (557995723423/1250000000000 : ℝ), (267015174043/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259608049/1250000000 : ℝ)|^533 ≤ (6318957128111/50000000000000 : ℝ)^405
        have hw : |(-259608049/1250000000 : ℝ)|=(259608049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2709008893/5000000000 : ℝ)|^533 ≤ (557995723423/1250000000000 : ℝ)^405
        have hw : |(2709008893/5000000000 : ℝ)|=(2709008893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240273319/10000000000 : ℝ)|^533 ≤ (267015174043/625000000000 : ℝ)^405
        have hw : |(5240273319/10000000000 : ℝ)|=(5240273319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s4_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5350469277/10000000000 : ℝ)*x 0 + (-2167523927/10000000000 : ℝ)*x 1 + (5240273331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350469277/10000000000 : ℝ)^533 ≤ (21954335597/50000000000 : ℝ)^405 := by
    have hnat : (5350469277 : ℕ)^533*50000000000^405 ≤ 21954335597^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350469277 10000000000 21954335597 50000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2167523927/10000000000 : ℝ)^533 ≤ (13368900804071/100000000000000 : ℝ)^405 := by
    have hnat : (2167523927 : ℕ)^533*100000000000000^405 ≤ 13368900804071^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167523927 10000000000 13368900804071 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240273331/10000000000 : ℝ)^533 ≤ (2670151748477/6250000000000 : ℝ)^405 := by
    have hnat : (5240273331 : ℕ)^533*6250000000000^405 ≤ 2670151748477^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240273331 10000000000 2670151748477 6250000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350469277/10000000000 : ℝ), (-2167523927/10000000000 : ℝ), (5240273331/10000000000 : ℝ)] ![(21954335597/50000000000 : ℝ), (13368900804071/100000000000000 : ℝ), (2670151748477/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350469277/10000000000 : ℝ)|^533 ≤ (21954335597/50000000000 : ℝ)^405
        have hw : |(5350469277/10000000000 : ℝ)|=(5350469277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2167523927/10000000000 : ℝ)|^533 ≤ (13368900804071/100000000000000 : ℝ)^405
        have hw : |(-2167523927/10000000000 : ℝ)|=(2167523927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240273331/10000000000 : ℝ)|^533 ≤ (2670151748477/6250000000000 : ℝ)^405
        have hw : |(5240273331/10000000000 : ℝ)|=(5240273331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s4_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1070093863/2000000000 : ℝ)*x 0 + (1048054649/2000000000 : ℝ)*x 1 + (-2167523991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070093863/2000000000 : ℝ)^533 ≤ (43908671604407/100000000000000 : ℝ)^405 := by
    have hnat : (1070093863 : ℕ)^533*100000000000000^405 ≤ 43908671604407^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070093863 2000000000 43908671604407 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048054649/2000000000 : ℝ)^533 ≤ (21361213526453/50000000000000 : ℝ)^405 := by
    have hnat : (1048054649 : ℕ)^533*50000000000000^405 ≤ 21361213526453^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048054649 2000000000 21361213526453 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2167523991/10000000000 : ℝ)^533 ≤ (13368901323569/100000000000000 : ℝ)^405 := by
    have hnat : (2167523991 : ℕ)^533*100000000000000^405 ≤ 13368901323569^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167523991 10000000000 13368901323569 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070093863/2000000000 : ℝ), (1048054649/2000000000 : ℝ), (-2167523991/10000000000 : ℝ)] ![(43908671604407/100000000000000 : ℝ), (21361213526453/50000000000000 : ℝ), (13368901323569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070093863/2000000000 : ℝ)|^533 ≤ (43908671604407/100000000000000 : ℝ)^405
        have hw : |(1070093863/2000000000 : ℝ)|=(1070093863/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048054649/2000000000 : ℝ)|^533 ≤ (21361213526453/50000000000000 : ℝ)^405
        have hw : |(1048054649/2000000000 : ℝ)|=(1048054649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2167523991/10000000000 : ℝ)|^533 ≤ (13368901323569/100000000000000 : ℝ)^405
        have hw : |(-2167523991/10000000000 : ℝ)|=(2167523991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s4_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4336419761/10000000000 : ℝ)*x 0 + (415661859/1000000000 : ℝ)*x 1 + (4523601487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336419761/10000000000 : ℝ)^533 ≤ (33300203756951/100000000000000 : ℝ)^405 := by
    have hnat : (4336419761 : ℕ)^533*100000000000000^405 ≤ 33300203756951^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336419761 10000000000 33300203756951 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415661859/1000000000 : ℝ)^533 ≤ (15747559131851/50000000000000 : ℝ)^405 := by
    have hnat : (415661859 : ℕ)^533*50000000000000^405 ≤ 15747559131851^405*1000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415661859 1000000000 15747559131851 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4523601487/10000000000 : ℝ)^533 ≤ (35204677959873/100000000000000 : ℝ)^405 := by
    have hnat : (4523601487 : ℕ)^533*100000000000000^405 ≤ 35204677959873^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523601487 10000000000 35204677959873 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336419761/10000000000 : ℝ), (415661859/1000000000 : ℝ), (4523601487/10000000000 : ℝ)] ![(33300203756951/100000000000000 : ℝ), (15747559131851/50000000000000 : ℝ), (35204677959873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336419761/10000000000 : ℝ)|^533 ≤ (33300203756951/100000000000000 : ℝ)^405
        have hw : |(4336419761/10000000000 : ℝ)|=(4336419761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(415661859/1000000000 : ℝ)|^533 ≤ (15747559131851/50000000000000 : ℝ)^405
        have hw : |(415661859/1000000000 : ℝ)|=(415661859/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4523601487/10000000000 : ℝ)|^533 ≤ (35204677959873/100000000000000 : ℝ)^405
        have hw : |(4523601487/10000000000 : ℝ)|=(4523601487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s4_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-415375683/2000000000 : ℝ)*x 0 + (1048186317/2000000000 : ℝ)*x 1 + (2708678021/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415375683/2000000000 : ℝ)^533 ≤ (1579753319563/12500000000000 : ℝ)^405 := by
    have hnat : (415375683 : ℕ)^533*12500000000000^405 ≤ 1579753319563^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415375683 2000000000 1579753319563 12500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048186317/2000000000 : ℝ)^533 ≤ (21364745382863/50000000000000 : ℝ)^405 := by
    have hnat : (1048186317 : ℕ)^533*50000000000000^405 ≤ 21364745382863^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048186317 2000000000 21364745382863 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708678021/5000000000 : ℝ)^533 ≤ (44632482669947/100000000000000 : ℝ)^405 := by
    have hnat : (2708678021 : ℕ)^533*100000000000000^405 ≤ 44632482669947^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708678021 5000000000 44632482669947 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-415375683/2000000000 : ℝ), (1048186317/2000000000 : ℝ), (2708678021/5000000000 : ℝ)] ![(1579753319563/12500000000000 : ℝ), (21364745382863/50000000000000 : ℝ), (44632482669947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-415375683/2000000000 : ℝ)|^533 ≤ (1579753319563/12500000000000 : ℝ)^405
        have hw : |(-415375683/2000000000 : ℝ)|=(415375683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048186317/2000000000 : ℝ)|^533 ≤ (21364745382863/50000000000000 : ℝ)^405
        have hw : |(1048186317/2000000000 : ℝ)|=(1048186317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708678021/5000000000 : ℝ)|^533 ≤ (44632482669947/100000000000000 : ℝ)^405
        have hw : |(2708678021/5000000000 : ℝ)|=(2708678021/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s4_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (165777929/312500000 : ℝ)*x 0 + (-124402569/625000000 : ℝ)*x 1 + (1083471187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165777929/312500000 : ℝ)^533 ≤ (5427138919501/12500000000000 : ℝ)^405 := by
    have hnat : (165777929 : ℕ)^533*12500000000000^405 ≤ 5427138919501^405*312500000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165777929 312500000 5427138919501 12500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124402569/625000000 : ℝ)^533 ≤ (2390081422559/20000000000000 : ℝ)^405 := by
    have hnat : (124402569 : ℕ)^533*20000000000000^405 ≤ 2390081422559^405*625000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124402569 625000000 2390081422559 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083471187/2000000000 : ℝ)^533 ≤ (44632481509783/100000000000000 : ℝ)^405 := by
    have hnat : (1083471187 : ℕ)^533*100000000000000^405 ≤ 44632481509783^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083471187 2000000000 44632481509783 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165777929/312500000 : ℝ), (-124402569/625000000 : ℝ), (1083471187/2000000000 : ℝ)] ![(5427138919501/12500000000000 : ℝ), (2390081422559/20000000000000 : ℝ), (44632481509783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165777929/312500000 : ℝ)|^533 ≤ (5427138919501/12500000000000 : ℝ)^405
        have hw : |(165777929/312500000 : ℝ)|=(165777929/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124402569/625000000 : ℝ)|^533 ≤ (2390081422559/20000000000000 : ℝ)^405
        have hw : |(-124402569/625000000 : ℝ)|=(124402569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083471187/2000000000 : ℝ)|^533 ≤ (44632481509783/100000000000000 : ℝ)^405
        have hw : |(1083471187/2000000000 : ℝ)|=(1083471187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s4_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5304893449/10000000000 : ℝ)*x 0 + (677169531/1250000000 : ℝ)*x 1 + (-62201283/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304893449/10000000000 : ℝ)^533 ≤ (2713569271931/6250000000000 : ℝ)^405 := by
    have hnat : (5304893449 : ℕ)^533*6250000000000^405 ≤ 2713569271931^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304893449 10000000000 2713569271931 6250000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677169531/1250000000 : ℝ)^533 ≤ (8926496980707/20000000000000 : ℝ)^405 := by
    have hnat : (677169531 : ℕ)^533*20000000000000^405 ≤ 8926496980707^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677169531 1250000000 8926496980707 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62201283/312500000 : ℝ)^533 ≤ (11950406733527/100000000000000 : ℝ)^405 := by
    have hnat : (62201283 : ℕ)^533*100000000000000^405 ≤ 11950406733527^405*312500000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62201283 312500000 11950406733527 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304893449/10000000000 : ℝ), (677169531/1250000000 : ℝ), (-62201283/312500000 : ℝ)] ![(2713569271931/6250000000000 : ℝ), (8926496980707/20000000000000 : ℝ), (11950406733527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304893449/10000000000 : ℝ)|^533 ≤ (2713569271931/6250000000000 : ℝ)^405
        have hw : |(5304893449/10000000000 : ℝ)|=(5304893449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677169531/1250000000 : ℝ)|^533 ≤ (8926496980707/20000000000000 : ℝ)^405
        have hw : |(677169531/1250000000 : ℝ)|=(677169531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-62201283/312500000 : ℝ)|^533 ≤ (11950406733527/100000000000000 : ℝ)^405
        have hw : |(-62201283/312500000 : ℝ)|=(62201283/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s4_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4336448733/10000000000 : ℝ)*x 0 + (36177941/80000000 : ℝ)*x 1 + (4157984779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4336448733/10000000000 : ℝ)^533 ≤ (33300496554001/100000000000000 : ℝ)^405 := by
    have hnat : (4336448733 : ℕ)^533*100000000000000^405 ≤ 33300496554001^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4336448733 10000000000 33300496554001 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36177941/80000000 : ℝ)^533 ≤ (35190761045351/100000000000000 : ℝ)^405 := by
    have hnat : (36177941 : ℕ)^533*100000000000000^405 ≤ 35190761045351^405*80000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36177941 80000000 35190761045351 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4157984779/10000000000 : ℝ)^533 ≤ (6301748477571/20000000000000 : ℝ)^405 := by
    have hnat : (4157984779 : ℕ)^533*20000000000000^405 ≤ 6301748477571^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4157984779 10000000000 6301748477571 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4336448733/10000000000 : ℝ), (36177941/80000000 : ℝ), (4157984779/10000000000 : ℝ)] ![(33300496554001/100000000000000 : ℝ), (35190761045351/100000000000000 : ℝ), (6301748477571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4336448733/10000000000 : ℝ)|^533 ≤ (33300496554001/100000000000000 : ℝ)^405
        have hw : |(4336448733/10000000000 : ℝ)|=(4336448733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36177941/80000000 : ℝ)|^533 ≤ (35190761045351/100000000000000 : ℝ)^405
        have hw : |(36177941/80000000 : ℝ)|=(36177941/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4157984779/10000000000 : ℝ)|^533 ≤ (6301748477571/20000000000000 : ℝ)^405
        have hw : |(4157984779/10000000000 : ℝ)|=(4157984779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1071/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10991/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (461/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1071/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15051/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1071/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1071/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15051/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1071/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1071/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15051/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1071/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1071/10000 : ℝ) ^ (4263/1024 : ℝ) ≤ (9139663147192357/100000000000000000000 : ℝ) := by
    have hpowers : (1071/10000 : ℝ)^4263 ≤ (9139663147192357/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1071 : ℕ)^4263*100000000000000000000^1024 ≤ 9139663147192357^1024*10000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1071 10000 9139663147192357 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1071/10000 : ℝ)) (X := (9139663147192357/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15051/100000 : ℝ) ^ (4263/1024 : ℝ) ≤ (117756237192813/312500000000000000 : ℝ) := by
    have hpowers : (15051/100000 : ℝ)^4263 ≤ (117756237192813/312500000000000000 : ℝ)^1024 := by
      have hnat : (15051 : ℕ)^4263*312500000000000000^1024 ≤ 117756237192813^1024*100000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15051 100000 117756237192813 312500000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15051/100000 : ℝ)) (X := (117756237192813/312500000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009139663147192357/50000000000000000000 : ℝ) ≤ (5000219525339393/5000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50009139663147192357/50000000000000000000 : ℝ)^1024 ≤ (5000219525339393/5000000000000000 : ℝ)^4263 := by
      have hnat : (50009139663147192357 : ℕ)^1024*5000000000000000^4263 ≤ 5000219525339393^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009139663147192357 50000000000000000000 5000219525339393 5000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000219525339393/5000000000000000 : ℝ)) (X := (50009139663147192357/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046821659048892517/100000000000000000000 : ℝ) ≤ (2000224897269399/2000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (100046821659048892517/100000000000000000000 : ℝ)^1024 ≤ (2000224897269399/2000000000000000 : ℝ)^4263 := by
      have hnat : (100046821659048892517 : ℕ)^1024*2000000000000000^4263 ≤ 2000224897269399^4263*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046821659048892517 100000000000000000000 2000224897269399 2000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000224897269399/2000000000000000 : ℝ)) (X := (100046821659048892517/100000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (156367756237192813/156250000000000000 : ℝ) ≤ (2500452480503801/2500000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (156367756237192813/156250000000000000 : ℝ)^1024 ≤ (2500452480503801/2500000000000000 : ℝ)^4263 := by
      have hnat : (156367756237192813 : ℕ)^1024*2500000000000000^4263 ≤ 2500452480503801^4263*156250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        156367756237192813 156250000000000000 2500452480503801 2500000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500452480503801/2500000000000000 : ℝ)) (X := (156367756237192813/156250000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9139663147192357/100000000000000000000 : ℝ) ≤ ((7232870647830595541/7235000000000000000 : ℝ)+2*(685435668209/434100000000000 : ℝ)*(1071/10000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (7232870647830595541/7235000000000000000 : ℝ)+2*(685435668209/434100000000000 : ℝ)*(1071/10000 : ℝ)=(5000219525339393/5000000000000000 : ℝ) by norm_num, show 1+2*(9139663147192357/100000000000000000000 : ℝ)=(50009139663147192357/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(117756237192813/312500000000000000 : ℝ)+(9139663147192357/100000000000000000000 : ℝ) ≤ ((7232870647830595541/7235000000000000000 : ℝ)+(685435668209/434100000000000 : ℝ)*((15051/100000 : ℝ)+(1071/10000 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (7232870647830595541/7235000000000000000 : ℝ)+(685435668209/434100000000000 : ℝ)*((15051/100000 : ℝ)+(1071/10000 : ℝ))=(2000224897269399/2000000000000000 : ℝ) by norm_num, show 1+(117756237192813/312500000000000000 : ℝ)+(9139663147192357/100000000000000000000 : ℝ)=(100046821659048892517/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(117756237192813/312500000000000000 : ℝ) ≤ ((7232870647830595541/7235000000000000000 : ℝ)+2*(685435668209/434100000000000 : ℝ)*(15051/100000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (7232870647830595541/7235000000000000000 : ℝ)+2*(685435668209/434100000000000 : ℝ)*(15051/100000 : ℝ)=(2500452480503801/2500000000000000 : ℝ) by norm_num, show 1+2*(117756237192813/312500000000000000 : ℝ)=(156367756237192813/156250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7232870647830595541/7235000000000000000 : ℝ)*(X 1 0+X 2 0)+(685435668209/434100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (1071/10000 : ℝ)) (hi := (15051/100000 : ℝ)) (c := (7232870647830595541/7235000000000000000 : ℝ)) (alpha := (685435668209/434100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7232870647830595541/7235000000000000000 : ℝ)*(X 0 1+X 2 1)+(685435668209/434100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (1071/10000 : ℝ)) (hi := (15051/100000 : ℝ)) (c := (7232870647830595541/7235000000000000000 : ℝ)) (alpha := (685435668209/434100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7232870647830595541/7235000000000000000 : ℝ)*(X 0 2+X 1 2)+(685435668209/434100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (1071/10000 : ℝ)) (hi := (15051/100000 : ℝ)) (c := (7232870647830595541/7235000000000000000 : ℝ)) (alpha := (685435668209/434100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-259608049/1250000000 : ℝ)*X 0 0+(2709008893/5000000000 : ℝ)*X 0 1+(5240273319/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350469277/10000000000 : ℝ)*X 1 0+(-2167523927/10000000000 : ℝ)*X 1 1+(5240273331/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070093863/2000000000 : ℝ)*X 2 0+(1048054649/2000000000 : ℝ)*X 2 1+(-2167523991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4336419761/10000000000 : ℝ)*X 0 0+(415661859/1000000000 : ℝ)*X 0 1+(4523601487/10000000000 : ℝ)*X 0 2+(4336419761/10000000000 : ℝ)*X 1 0+(415661859/1000000000 : ℝ)*X 1 1+(4523601487/10000000000 : ℝ)*X 1 2+(4336419761/10000000000 : ℝ)*X 2 0+(415661859/1000000000 : ℝ)*X 2 1+(4523601487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-415375683/2000000000 : ℝ)*X 0 0+(1048186317/2000000000 : ℝ)*X 0 1+(2708678021/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165777929/312500000 : ℝ)*X 1 0+(-124402569/625000000 : ℝ)*X 1 1+(1083471187/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5304893449/10000000000 : ℝ)*X 2 0+(677169531/1250000000 : ℝ)*X 2 1+(-62201283/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4336448733/10000000000 : ℝ)*X 0 0+(36177941/80000000 : ℝ)*X 0 1+(4157984779/10000000000 : ℝ)*X 0 2+(4336448733/10000000000 : ℝ)*X 1 0+(36177941/80000000 : ℝ)*X 1 1+(4157984779/10000000000 : ℝ)*X 1 2+(4336448733/10000000000 : ℝ)*X 2 0+(36177941/80000000 : ℝ)*X 2 1+(4157984779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (384431076497325373369665627/180875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19796969/4000000000000 : ℝ)*(base19) + (264982079/50000000000000 : ℝ)*(base23) + (11217021/12500000000000 : ℝ)*(upper3) + (263107/10000000000000 : ℝ)*(upper4) + (4858187/25000000000000 : ℝ)*(upper5) + (2087751600576417/50000000000000 : ℝ)*(major0) + (2087751600576417/50000000000000 : ℝ)*(major1) + (2087751600576417/50000000000000 : ℝ)*(major2) + (703258111935793/12500000000000 : ℝ)*(sp0) + (2813036508593027/50000000000000 : ℝ)*(sp1) + (5626072982146121/100000000000000 : ℝ)*(sp2) + (2724927131631789/100000000000000 : ℝ)*(sp3) + (1723324787/20000000000000 : ℝ)*(sp4) + (2843858523/50000000000000 : ℝ)*(sp7) + (681233204837209/25000000000000 : ℝ)*(f.failure) + (5626073512110279/100000000000000 : ℝ)*(f.sum) + (3491362353661/904375000000000000000000000 : ℝ)*base66 + (1379120043519256597/361750000000000000000000000000000 : ℝ)*base67 + (2680845054917256597/361750000000000000000000000000000 : ℝ)*base69 + (768484782458756597/361750000000000000000000000000000 : ℝ)*base71 + (107938288801/226093750000000000000000000 : ℝ)*base73 + (678484693918256597/361750000000000000000000000000000 : ℝ)*base75 + (4987606086164006597/361750000000000000000000000000000 : ℝ)*base77 + (1148963375808756597/361750000000000000000000000000000 : ℝ)*base79 + (6738878044273/1808750000000000000000000000 : ℝ)*base81 + (20510877/2500000000000000000000 : ℝ)*base89 + (20510877/2500000000000000000000 : ℝ)*base91 + (20510877/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (742026335656959936949554379/180875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65803851/6250000000000 : ℝ)*(base19) + (818603723/100000000000000 : ℝ)*(base23) + (123203429/100000000000000 : ℝ)*(upper3) + (4048311/25000000000000 : ℝ)*(lower4) + (19077501/100000000000000 : ℝ)*(upper5) + (2103362758542791/50000000000000 : ℝ)*(major0) + (2103362758542791/50000000000000 : ℝ)*(major1) + (2103362758542791/50000000000000 : ℝ)*(major2) + (16864245407/100000000000000 : ℝ)*(sp1) + (20742624643/100000000000000 : ℝ)*(sp2) + (2834071199478589/50000000000000 : ℝ)*(sp4) + (1133624896370031/20000000000000 : ℝ)*(sp5) + (1417030209432203/25000000000000 : ℝ)*(sp6) + (2745308498466441/100000000000000 : ℝ)*(sp7) + (2745308498466441/100000000000000 : ℝ)*(f.failure) + (2834071199478589/50000000000000 : ℝ)*(f.sum) + (31166256369623/21705000000000000000000000000 : ℝ)*base65 + (6031049384710915207/1085250000000000000000000000000000 : ℝ)*base68 + (1635522365875915207/1085250000000000000000000000000000 : ℝ)*base70 + (2425461534025165207/1085250000000000000000000000000000 : ℝ)*base72 + (56576954870321/10852500000000000000000000000 : ℝ)*base74 + (21141470703777415207/1085250000000000000000000000000000 : ℝ)*base76 + (7541865663503665207/1085250000000000000000000000000000 : ℝ)*base78 + (2086954373791165207/1085250000000000000000000000000000 : ℝ)*base80 + (3489602850049/678281250000000000000000000 : ℝ)*base81 + (65762573/10000000000000000000000 : ℝ)*base89 + (65762573/10000000000000000000000 : ℝ)*base91 + (65762573/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1304_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15051/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1071/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10991/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (461/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1304_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1304_s5_0 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1038596661/5000000000 : ℝ)*x 0 + (5415206853/10000000000 : ℝ)*x 1 + (1310717023/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038596661/5000000000 : ℝ)^533 ≤ (12640548486903/100000000000000 : ℝ)^405 := by
    have hnat : (1038596661 : ℕ)^533*100000000000000^405 ≤ 12640548486903^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038596661 5000000000 12640548486903 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415206853/10000000000 : ℝ)^533 ≤ (44609181204747/100000000000000 : ℝ)^405 := by
    have hnat : (5415206853 : ℕ)^533*100000000000000^405 ≤ 44609181204747^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415206853 10000000000 44609181204747 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310717023/2500000000 : ℝ)^533 ≤ (1335945946919/3125000000000 : ℝ)^405 := by
    have hnat : (1310717023 : ℕ)^533*3125000000000^405 ≤ 1335945946919^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310717023 2500000000 1335945946919 3125000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1038596661/5000000000 : ℝ), (5415206853/10000000000 : ℝ), (1310717023/2500000000 : ℝ)] ![(12640548486903/100000000000000 : ℝ), (44609181204747/100000000000000 : ℝ), (1335945946919/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1038596661/5000000000 : ℝ)|^533 ≤ (12640548486903/100000000000000 : ℝ)^405
        have hw : |(-1038596661/5000000000 : ℝ)|=(1038596661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415206853/10000000000 : ℝ)|^533 ≤ (44609181204747/100000000000000 : ℝ)^405
        have hw : |(5415206853/10000000000 : ℝ)|=(5415206853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310717023/2500000000 : ℝ)|^533 ≤ (1335945946919/3125000000000 : ℝ)^405
        have hw : |(1310717023/2500000000 : ℝ)|=(1310717023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s5_1 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2674877767/5000000000 : ℝ)*x 0 + (-216504313/1000000000 : ℝ)*x 1 + (131071701/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674877767/5000000000 : ℝ)^533 ≤ (1097524070263/2500000000000 : ℝ)^405 := by
    have hnat : (2674877767 : ℕ)^533*2500000000000^405 ≤ 1097524070263^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674877767 5000000000 1097524070263 2500000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216504313/1000000000 : ℝ)^533 ≤ (166859592831/1250000000000 : ℝ)^405 := by
    have hnat : (216504313 : ℕ)^533*1250000000000^405 ≤ 166859592831^405*1000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216504313 1000000000 166859592831 1250000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131071701/250000000 : ℝ)^533 ≤ (42750269743393/100000000000000 : ℝ)^405 := by
    have hnat : (131071701 : ℕ)^533*100000000000000^405 ≤ 42750269743393^405*250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131071701 250000000 42750269743393 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674877767/5000000000 : ℝ), (-216504313/1000000000 : ℝ), (131071701/250000000 : ℝ)] ![(1097524070263/2500000000000 : ℝ), (166859592831/1250000000000 : ℝ), (42750269743393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674877767/5000000000 : ℝ)|^533 ≤ (1097524070263/2500000000000 : ℝ)^405
        have hw : |(2674877767/5000000000 : ℝ)|=(2674877767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-216504313/1000000000 : ℝ)|^533 ≤ (166859592831/1250000000000 : ℝ)^405
        have hw : |(-216504313/1000000000 : ℝ)|=(216504313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131071701/250000000 : ℝ)|^533 ≤ (42750269743393/100000000000000 : ℝ)^405
        have hw : |(131071701/250000000 : ℝ)|=(131071701/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s5_2 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1337438859/2500000000 : ℝ)*x 0 + (104857363/200000000 : ℝ)*x 1 + (-541260779/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337438859/2500000000 : ℝ)^533 ≤ (10975240438037/25000000000000 : ℝ)^405 := by
    have hnat : (1337438859 : ℕ)^533*25000000000000^405 ≤ 10975240438037^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337438859 2500000000 10975240438037 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104857363/200000000 : ℝ)^533 ≤ (1335945966369/3125000000000 : ℝ)^405 := by
    have hnat : (104857363 : ℕ)^533*3125000000000^405 ≤ 1335945966369^405*200000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104857363 200000000 1335945966369 3125000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541260779/2500000000 : ℝ)^533 ≤ (13348767312881/100000000000000 : ℝ)^405 := by
    have hnat : (541260779 : ℕ)^533*100000000000000^405 ≤ 13348767312881^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541260779 2500000000 13348767312881 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337438859/2500000000 : ℝ), (104857363/200000000 : ℝ), (-541260779/2500000000 : ℝ)] ![(10975240438037/25000000000000 : ℝ), (1335945966369/3125000000000 : ℝ), (13348767312881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337438859/2500000000 : ℝ)|^533 ≤ (10975240438037/25000000000000 : ℝ)^405
        have hw : |(1337438859/2500000000 : ℝ)|=(1337438859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(104857363/200000000 : ℝ)|^533 ≤ (1335945966369/3125000000000 : ℝ)^405
        have hw : |(104857363/200000000 : ℝ)|=(104857363/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-541260779/2500000000 : ℝ)|^533 ≤ (13348767312881/100000000000000 : ℝ)^405
        have hw : |(-541260779/2500000000 : ℝ)|=(541260779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s5_3 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (542076983/1250000000 : ℝ)*x 0 + (1040543647/2500000000 : ℝ)*x 1 + (903599269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (542076983/1250000000 : ℝ)^533 ≤ (16651092813337/50000000000000 : ℝ)^405 := by
    have hnat : (542076983 : ℕ)^533*50000000000000^405 ≤ 16651092813337^405*1250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542076983 1250000000 16651092813337 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040543647/2500000000 : ℝ)^533 ≤ (15775266739887/50000000000000 : ℝ)^405 := by
    have hnat : (1040543647 : ℕ)^533*50000000000000^405 ≤ 15775266739887^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040543647 2500000000 15775266739887 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (903599269/2000000000 : ℝ)^533 ≤ (7029456176659/20000000000000 : ℝ)^405 := by
    have hnat : (903599269 : ℕ)^533*20000000000000^405 ≤ 7029456176659^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903599269 2000000000 7029456176659 20000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(542076983/1250000000 : ℝ), (1040543647/2500000000 : ℝ), (903599269/2000000000 : ℝ)] ![(16651092813337/50000000000000 : ℝ), (15775266739887/50000000000000 : ℝ), (7029456176659/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(542076983/1250000000 : ℝ)|^533 ≤ (16651092813337/50000000000000 : ℝ)^405
        have hw : |(542076983/1250000000 : ℝ)|=(542076983/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1040543647/2500000000 : ℝ)|^533 ≤ (15775266739887/50000000000000 : ℝ)^405
        have hw : |(1040543647/2500000000 : ℝ)|=(1040543647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(903599269/2000000000 : ℝ)|^533 ≤ (7029456176659/20000000000000 : ℝ)^405
        have hw : |(903599269/2000000000 : ℝ)|=(903599269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s5_4 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2077206189/10000000000 : ℝ)*x 0 + (5243486987/10000000000 : ℝ)*x 1 + (5414584723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077206189/10000000000 : ℝ)^533 ≤ (3160162883687/25000000000000 : ℝ)^405 := by
    have hnat : (2077206189 : ℕ)^533*25000000000000^405 ≤ 3160162883687^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077206189 10000000000 3160162883687 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243486987/10000000000 : ℝ)^533 ≤ (10689227954243/25000000000000 : ℝ)^405 := by
    have hnat : (5243486987 : ℕ)^533*25000000000000^405 ≤ 10689227954243^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243486987 10000000000 10689227954243 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414584723/10000000000 : ℝ)^533 ≤ (44602436628847/100000000000000 : ℝ)^405 := by
    have hnat : (5414584723 : ℕ)^533*100000000000000^405 ≤ 44602436628847^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414584723 10000000000 44602436628847 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2077206189/10000000000 : ℝ), (5243486987/10000000000 : ℝ), (5414584723/10000000000 : ℝ)] ![(3160162883687/25000000000000 : ℝ), (10689227954243/25000000000000 : ℝ), (44602436628847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2077206189/10000000000 : ℝ)|^533 ≤ (3160162883687/25000000000000 : ℝ)^405
        have hw : |(-2077206189/10000000000 : ℝ)|=(2077206189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243486987/10000000000 : ℝ)|^533 ≤ (10689227954243/25000000000000 : ℝ)^405
        have hw : |(5243486987/10000000000 : ℝ)|=(5243486987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414584723/10000000000 : ℝ)|^533 ≤ (44602436628847/100000000000000 : ℝ)^405
        have hw : |(5414584723/10000000000 : ℝ)|=(5414584723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s5_5 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5305566053/10000000000 : ℝ)*x 0 + (-1993326487/10000000000 : ℝ)*x 1 + (1082916931/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305566053/10000000000 : ℝ)^533 ≤ (43424353120233/100000000000000 : ℝ)^405 := by
    have hnat : (5305566053 : ℕ)^533*100000000000000^405 ≤ 43424353120233^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305566053 10000000000 43424353120233 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1993326487/10000000000 : ℝ)^533 ≤ (11973210978021/100000000000000 : ℝ)^405 := by
    have hnat : (1993326487 : ℕ)^533*100000000000000^405 ≤ 11973210978021^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993326487 10000000000 11973210978021 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082916931/2000000000 : ℝ)^533 ≤ (22301217945833/50000000000000 : ℝ)^405 := by
    have hnat : (1082916931 : ℕ)^533*50000000000000^405 ≤ 22301217945833^405*2000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082916931 2000000000 22301217945833 50000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305566053/10000000000 : ℝ), (-1993326487/10000000000 : ℝ), (1082916931/2000000000 : ℝ)] ![(43424353120233/100000000000000 : ℝ), (11973210978021/100000000000000 : ℝ), (22301217945833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305566053/10000000000 : ℝ)|^533 ≤ (43424353120233/100000000000000 : ℝ)^405
        have hw : |(5305566053/10000000000 : ℝ)|=(5305566053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1993326487/10000000000 : ℝ)|^533 ≤ (11973210978021/100000000000000 : ℝ)^405
        have hw : |(-1993326487/10000000000 : ℝ)|=(1993326487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082916931/2000000000 : ℝ)|^533 ≤ (22301217945833/50000000000000 : ℝ)^405
        have hw : |(1082916931/2000000000 : ℝ)|=(1082916931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s5_6 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2652782981/5000000000 : ℝ)*x 0 + (135364619/250000000 : ℝ)*x 1 + (-1993326467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652782981/5000000000 : ℝ)^533 ≤ (169626375547/390625000000 : ℝ)^405 := by
    have hnat : (2652782981 : ℕ)^533*390625000000^405 ≤ 169626375547^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652782981 5000000000 169626375547 390625000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135364619/250000000 : ℝ)^533 ≤ (44602437029961/100000000000000 : ℝ)^405 := by
    have hnat : (135364619 : ℕ)^533*100000000000000^405 ≤ 44602437029961^405*250000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135364619 250000000 44602437029961 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1993326467/10000000000 : ℝ)^533 ≤ (149665135249/1250000000000 : ℝ)^405 := by
    have hnat : (1993326467 : ℕ)^533*1250000000000^405 ≤ 149665135249^405*10000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993326467 10000000000 149665135249 1250000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652782981/5000000000 : ℝ), (135364619/250000000 : ℝ), (-1993326467/10000000000 : ℝ)] ![(169626375547/390625000000 : ℝ), (44602437029961/100000000000000 : ℝ), (149665135249/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652782981/5000000000 : ℝ)|^533 ≤ (169626375547/390625000000 : ℝ)^405
        have hw : |(2652782981/5000000000 : ℝ)|=(2652782981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135364619/250000000 : ℝ)|^533 ≤ (44602437029961/100000000000000 : ℝ)^405
        have hw : |(135364619/250000000 : ℝ)|=(135364619/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1993326467/10000000000 : ℝ)|^533 ≤ (149665135249/1250000000000 : ℝ)^405
        have hw : |(-1993326467/10000000000 : ℝ)|=(1993326467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1304_s5_7 (p : ℝ) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ)) (x : Fin 3 → ℝ) :
    (271040153/625000000 : ℝ)*x 0 + (2258359263/5000000000 : ℝ)*x 1 + (1040864729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271040153/625000000 : ℝ)^533 ≤ (8325613573479/25000000000000 : ℝ)^405 := by
    have hnat : (271040153 : ℕ)^533*25000000000000^405 ≤ 8325613573479^405*625000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271040153 625000000 8325613573479 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2258359263/5000000000 : ℝ)^533 ≤ (35134199069231/100000000000000 : ℝ)^405 := by
    have hnat : (2258359263 : ℕ)^533*100000000000000^405 ≤ 35134199069231^405*5000000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258359263 5000000000 35134199069231 100000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040864729/2500000000 : ℝ)^533 ≤ (7890836656079/25000000000000 : ℝ)^405 := by
    have hnat : (1040864729 : ℕ)^533*25000000000000^405 ≤ 7890836656079^405*2500000000^533 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040864729 2500000000 7890836656079 25000000000000 533 405 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (533/128 : ℝ)) 533 405 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271040153/625000000 : ℝ), (2258359263/5000000000 : ℝ), (1040864729/2500000000 : ℝ)] ![(8325613573479/25000000000000 : ℝ), (35134199069231/100000000000000 : ℝ), (7890836656079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271040153/625000000 : ℝ)|^533 ≤ (8325613573479/25000000000000 : ℝ)^405
        have hw : |(271040153/625000000 : ℝ)|=(271040153/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2258359263/5000000000 : ℝ)|^533 ≤ (35134199069231/100000000000000 : ℝ)^405
        have hw : |(2258359263/5000000000 : ℝ)|=(2258359263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1040864729/2500000000 : ℝ)|^533 ≤ (7890836656079/25000000000000 : ℝ)^405
        have hw : |(1040864729/2500000000 : ℝ)|=(1040864729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1304_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10991/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5523/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14693/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10991/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (461/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10991/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10991/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (461/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10991/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10991/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (461/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10991/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10991/100000 : ℝ) ^ (4263/1024 : ℝ) ≤ (10180180667483179/100000000000000000000 : ℝ) := by
    have hpowers : (10991/100000 : ℝ)^4263 ≤ (10180180667483179/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10991 : ℕ)^4263*100000000000000000000^1024 ≤ 10180180667483179^1024*100000^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10991 100000 10180180667483179 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10991/100000 : ℝ)) (X := (10180180667483179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (461/3125 : ℝ) ^ (4263/1024 : ℝ) ≤ (34662101149534789/100000000000000000000 : ℝ) := by
    have hpowers : (461/3125 : ℝ)^4263 ≤ (34662101149534789/100000000000000000000 : ℝ)^1024 := by
      have hnat : (461 : ℕ)^4263*100000000000000000000^1024 ≤ 34662101149534789^1024*3125^4263 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        461 3125 34662101149534789 100000000000000000000 4263 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (461/3125 : ℝ)) (X := (34662101149534789/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010180180667483179/50000000000000000000 : ℝ) ≤ (5000244515570759/5000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50010180180667483179/50000000000000000000 : ℝ)^1024 ≤ (5000244515570759/5000000000000000 : ℝ)^4263 := by
      have hnat : (50010180180667483179 : ℕ)^1024*5000000000000000^4263 ≤ 5000244515570759^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010180180667483179 50000000000000000000 5000244515570759 5000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000244515570759/5000000000000000 : ℝ)) (X := (50010180180667483179/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252802642613563623/6250000000000000000 : ℝ) ≤ (10001076956983821/10000000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (6252802642613563623/6250000000000000000 : ℝ)^1024 ≤ (10001076956983821/10000000000000000 : ℝ)^4263 := by
      have hnat : (6252802642613563623 : ℕ)^1024*10000000000000000^4263 ≤ 10001076956983821^4263*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252802642613563623 6250000000000000000 10001076956983821 10000000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001076956983821/10000000000000000 : ℝ)) (X := (6252802642613563623/6250000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034662101149534789/50000000000000000000 : ℝ) ≤ (2500416220706531/2500000000000000 : ℝ) ^ (4263/1024 : ℝ) := by
    have hpowers : (50034662101149534789/50000000000000000000 : ℝ)^1024 ≤ (2500416220706531/2500000000000000 : ℝ)^4263 := by
      have hnat : (50034662101149534789 : ℕ)^1024*2500000000000000^4263 ≤ 2500416220706531^4263*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034662101149534789 50000000000000000000 2500416220706531 2500000000000000 1024 4263 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500416220706531/2500000000000000 : ℝ)) (X := (50034662101149534789/50000000000000000000 : ℝ)) (by norm_num) 4263 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10180180667483179/100000000000000000000 : ℝ) ≤ ((9399728865064436163/9402500000000000000 : ℝ)+2*(587925842303/376100000000000 : ℝ)*(10991/100000 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (9399728865064436163/9402500000000000000 : ℝ)+2*(587925842303/376100000000000 : ℝ)*(10991/100000 : ℝ)=(5000244515570759/5000000000000000 : ℝ) by norm_num, show 1+2*(10180180667483179/100000000000000000000 : ℝ)=(50010180180667483179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34662101149534789/100000000000000000000 : ℝ)+(10180180667483179/100000000000000000000 : ℝ) ≤ ((9399728865064436163/9402500000000000000 : ℝ)+(587925842303/376100000000000 : ℝ)*((461/3125 : ℝ)+(10991/100000 : ℝ)))^(4263/1024 : ℝ) := by
    rw [show (9399728865064436163/9402500000000000000 : ℝ)+(587925842303/376100000000000 : ℝ)*((461/3125 : ℝ)+(10991/100000 : ℝ))=(10001076956983821/10000000000000000 : ℝ) by norm_num, show 1+(34662101149534789/100000000000000000000 : ℝ)+(10180180667483179/100000000000000000000 : ℝ)=(6252802642613563623/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34662101149534789/100000000000000000000 : ℝ) ≤ ((9399728865064436163/9402500000000000000 : ℝ)+2*(587925842303/376100000000000 : ℝ)*(461/3125 : ℝ))^(4263/1024 : ℝ) := by
    rw [show (9399728865064436163/9402500000000000000 : ℝ)+2*(587925842303/376100000000000 : ℝ)*(461/3125 : ℝ)=(2500416220706531/2500000000000000 : ℝ) by norm_num, show 1+2*(34662101149534789/100000000000000000000 : ℝ)=(50034662101149534789/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9399728865064436163/9402500000000000000 : ℝ)*(X 1 0+X 2 0)+(587925842303/376100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (10991/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (9399728865064436163/9402500000000000000 : ℝ)) (alpha := (587925842303/376100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9399728865064436163/9402500000000000000 : ℝ)*(X 0 1+X 2 1)+(587925842303/376100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (10991/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (9399728865064436163/9402500000000000000 : ℝ)) (alpha := (587925842303/376100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9399728865064436163/9402500000000000000 : ℝ)*(X 0 2+X 1 2)+(587925842303/376100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4263/1024 : ℝ)) (lo := (10991/100000 : ℝ)) (hi := (461/3125 : ℝ)) (c := (9399728865064436163/9402500000000000000 : ℝ)) (alpha := (587925842303/376100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1038596661/5000000000 : ℝ)*X 0 0+(5415206853/10000000000 : ℝ)*X 0 1+(1310717023/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674877767/5000000000 : ℝ)*X 1 0+(-216504313/1000000000 : ℝ)*X 1 1+(131071701/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337438859/2500000000 : ℝ)*X 2 0+(104857363/200000000 : ℝ)*X 2 1+(-541260779/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((542076983/1250000000 : ℝ)*X 0 0+(1040543647/2500000000 : ℝ)*X 0 1+(903599269/2000000000 : ℝ)*X 0 2+(542076983/1250000000 : ℝ)*X 1 0+(1040543647/2500000000 : ℝ)*X 1 1+(903599269/2000000000 : ℝ)*X 1 2+(542076983/1250000000 : ℝ)*X 2 0+(1040543647/2500000000 : ℝ)*X 2 1+(903599269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2077206189/10000000000 : ℝ)*X 0 0+(5243486987/10000000000 : ℝ)*X 0 1+(5414584723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305566053/10000000000 : ℝ)*X 1 0+(-1993326487/10000000000 : ℝ)*X 1 1+(1082916931/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652782981/5000000000 : ℝ)*X 2 0+(135364619/250000000 : ℝ)*X 2 1+(-1993326467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((271040153/625000000 : ℝ)*X 0 0+(2258359263/5000000000 : ℝ)*X 0 1+(1040864729/2500000000 : ℝ)*X 0 2+(271040153/625000000 : ℝ)*X 1 0+(2258359263/5000000000 : ℝ)*X 1 1+(1040864729/2500000000 : ℝ)*X 1 2+(271040153/625000000 : ℝ)*X 2 0+(2258359263/5000000000 : ℝ)*X 2 1+(1040864729/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1304_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1499652784748289940851620127/235062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (230144779/20000000000000 : ℝ)*(base19) + (946193683/100000000000000 : ℝ)*(base23) + (26276733/50000000000000 : ℝ)*(lower2) + (6714031/5000000000000 : ℝ)*(upper3) + (59379903/100000000000000 : ℝ)*(upper5) + (4306495213885943/100000000000000 : ℝ)*(major0) + (4306495213885943/100000000000000 : ℝ)*(major1) + (4306495213885943/100000000000000 : ℝ)*(major2) + (5802549724235949/100000000000000 : ℝ)*(sp0) + (2901285437701239/50000000000000 : ℝ)*(sp1) + (580257107993269/10000000000000 : ℝ)*(sp2) + (562081289593791/20000000000000 : ℝ)*(sp3) + (892075617/4000000000000 : ℝ)*(sp4) + (5870508199/50000000000000 : ℝ)*(sp7) + (351302273623169/12500000000000 : ℝ)*(f.failure) + (2901286013063187/50000000000000 : ℝ)*(f.sum) + (16514226526419/4701250000000000000000000000 : ℝ)*base66 + (3190294573460218291/940250000000000000000000000000000 : ℝ)*base68 + (9999141055441718291/940250000000000000000000000000000 : ℝ)*base70 + (7452555779204218291/940250000000000000000000000000000 : ℝ)*base72 + (54049928840589/18805000000000000000000000000 : ℝ)*base73 + (10003185953144031709/940250000000000000000000000000000 : ℝ)*base75 + (14677238939321218291/940250000000000000000000000000000 : ℝ)*base78 + (7274426086162218291/940250000000000000000000000000000 : ℝ)*base80 + (7195276884843/9402500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5461243/1250000000000000000000 : ℝ)*base90 + (5461243/1250000000000000000000 : ℝ)*base92 + (5461243/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17129091645118362317062293/9402500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84852221/20000000000000 : ℝ)*(base19) + (38907579/10000000000000 : ℝ)*(base23) + (42203131/100000000000000 : ℝ)*(upper3) + (26134487/100000000000000 : ℝ)*(lower4) + (20948883/100000000000000 : ℝ)*(upper5) + (86753899101279/2000000000000 : ℝ)*(major0) + (86753899101279/2000000000000 : ℝ)*(major1) + (86753899101279/2000000000000 : ℝ)*(major2) + (1639253909/25000000000000 : ℝ)*(sp1) + (8454225531/100000000000000 : ℝ)*(sp2) + (584461071358149/10000000000000 : ℝ)*(sp4) + (5844603732304749/100000000000000 : ℝ)*(sp5) + (5844601870280169/100000000000000 : ℝ)*(sp6) + (1415389567910547/50000000000000 : ℝ)*(sp7) + (1415389567910547/50000000000000 : ℝ)*(f.failure) + (584461071358149/10000000000000 : ℝ)*(f.sum) + (1508533687163/940250000000000000000000000 : ℝ)*base66 + (49188947375992523/18805000000000000000000000000000 : ℝ)*base68 + (86904129382492523/18805000000000000000000000000000 : ℝ)*base70 + (66405965901987523/18805000000000000000000000000000 : ℝ)*base72 + (4300552568391/3761000000000000000000000000 : ℝ)*base74 + (333515207978317523/18805000000000000000000000000000 : ℝ)*base76 + (155290219978252523/18805000000000000000000000000000 : ℝ)*base78 + (282658503281292523/18805000000000000000000000000000 : ℝ)*base80 + (4237358070163/752200000000000000000000000 : ℝ)*base82 + (29819391/5000000000000000000000 : ℝ)*base89 + (29819391/5000000000000000000000 : ℝ)*base91 + (29819391/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1304_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (461/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10991/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1304_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1304_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16263/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1304_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1304_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1304_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4263/1024 : ℝ) ≤ p) (hpb : p ≤ (533/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153233253/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16263/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1199/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5523/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14693/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1304_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
