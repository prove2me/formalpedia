-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1640_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:10:44.014518+00:00
-- url     : https://prove2.me/submissions/c3d1d7e5-9018-4bbf-96f8-34b5b144f502

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
theorem support_rectangle_w1640_s0_0 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1510367253/10000000000 : ℝ)*x 0 + (5797824137/10000000000 : ℝ)*x 1 + (307167703/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1510367253/10000000000 : ℝ)^4879 ≤ (4570808677089/50000000000000 : ℝ)^3855 := by
    have hnat : (1510367253 : ℕ)^4879*50000000000000^3855 ≤ 4570808677089^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1510367253 10000000000 4570808677089 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5797824137/10000000000 : ℝ)^4879 ≤ (25081375978579/50000000000000 : ℝ)^3855 := by
    have hnat : (5797824137 : ℕ)^4879*50000000000000^3855 ≤ 25081375978579^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5797824137 10000000000 25081375978579 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (307167703/625000000 : ℝ)^4879 ≤ (20347815332883/50000000000000 : ℝ)^3855 := by
    have hnat : (307167703 : ℕ)^4879*50000000000000^3855 ≤ 20347815332883^3855*625000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      307167703 625000000 20347815332883 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1510367253/10000000000 : ℝ), (5797824137/10000000000 : ℝ), (307167703/625000000 : ℝ)] ![(4570808677089/50000000000000 : ℝ), (25081375978579/50000000000000 : ℝ), (20347815332883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1510367253/10000000000 : ℝ)|^4879 ≤ (4570808677089/50000000000000 : ℝ)^3855
        have hw : |(-1510367253/10000000000 : ℝ)|=(1510367253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5797824137/10000000000 : ℝ)|^4879 ≤ (25081375978579/50000000000000 : ℝ)^3855
        have hw : |(5797824137/10000000000 : ℝ)|=(5797824137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(307167703/625000000 : ℝ)|^4879 ≤ (20347815332883/50000000000000 : ℝ)^3855
        have hw : |(307167703/625000000 : ℝ)|=(307167703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s0_1 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1360380363/2500000000 : ℝ)*x 0 + (-1996156293/10000000000 : ℝ)*x 1 + (4914684747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1360380363/2500000000 : ℝ)^4879 ≤ (46293497290921/100000000000000 : ℝ)^3855 := by
    have hnat : (1360380363 : ℕ)^4879*100000000000000^3855 ≤ 46293497290921^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360380363 2500000000 46293497290921 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1996156293/10000000000 : ℝ)^4879 ≤ (6505428161893/50000000000000 : ℝ)^3855 := by
    have hnat : (1996156293 : ℕ)^4879*50000000000000^3855 ≤ 6505428161893^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1996156293 10000000000 6505428161893 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4914684747/10000000000 : ℝ)^4879 ≤ (40695646375193/100000000000000 : ℝ)^3855 := by
    have hnat : (4914684747 : ℕ)^4879*100000000000000^3855 ≤ 40695646375193^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4914684747 10000000000 40695646375193 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1360380363/2500000000 : ℝ), (-1996156293/10000000000 : ℝ), (4914684747/10000000000 : ℝ)] ![(46293497290921/100000000000000 : ℝ), (6505428161893/50000000000000 : ℝ), (40695646375193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1360380363/2500000000 : ℝ)|^4879 ≤ (46293497290921/100000000000000 : ℝ)^3855
        have hw : |(1360380363/2500000000 : ℝ)|=(1360380363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1996156293/10000000000 : ℝ)|^4879 ≤ (6505428161893/50000000000000 : ℝ)^3855
        have hw : |(-1996156293/10000000000 : ℝ)|=(1996156293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4914684747/10000000000 : ℝ)|^4879 ≤ (40695646375193/100000000000000 : ℝ)^3855
        have hw : |(4914684747/10000000000 : ℝ)|=(4914684747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s0_2 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5441523363/10000000000 : ℝ)*x 0 + (2457341607/5000000000 : ℝ)*x 1 + (-399231149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5441523363/10000000000 : ℝ)^4879 ≤ (23146758933599/50000000000000 : ℝ)^3855 := by
    have hnat : (5441523363 : ℕ)^4879*50000000000000^3855 ≤ 23146758933599^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441523363 10000000000 23146758933599 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2457341607/5000000000 : ℝ)^4879 ≤ (5086953788681/12500000000000 : ℝ)^3855 := by
    have hnat : (2457341607 : ℕ)^4879*12500000000000^3855 ≤ 5086953788681^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2457341607 5000000000 5086953788681 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399231149/2000000000 : ℝ)^4879 ≤ (13010851803163/100000000000000 : ℝ)^3855 := by
    have hnat : (399231149 : ℕ)^4879*100000000000000^3855 ≤ 13010851803163^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399231149 2000000000 13010851803163 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5441523363/10000000000 : ℝ), (2457341607/5000000000 : ℝ), (-399231149/2000000000 : ℝ)] ![(23146758933599/50000000000000 : ℝ), (5086953788681/12500000000000 : ℝ), (13010851803163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5441523363/10000000000 : ℝ)|^4879 ≤ (23146758933599/50000000000000 : ℝ)^3855
        have hw : |(5441523363/10000000000 : ℝ)|=(5441523363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2457341607/5000000000 : ℝ)|^4879 ≤ (5086953788681/12500000000000 : ℝ)^3855
        have hw : |(2457341607/5000000000 : ℝ)|=(2457341607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399231149/2000000000 : ℝ)|^4879 ≤ (13010851803163/100000000000000 : ℝ)^3855
        have hw : |(-399231149/2000000000 : ℝ)|=(399231149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s0_3 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (255957611/625000000 : ℝ)*x 0 + (3080218189/10000000000 : ℝ)*x 1 + (5336361661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255957611/625000000 : ℝ)^4879 ≤ (32307285333509/100000000000000 : ℝ)^3855 := by
    have hnat : (255957611 : ℕ)^4879*100000000000000^3855 ≤ 32307285333509^3855*625000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255957611 625000000 32307285333509 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3080218189/10000000000 : ℝ)^4879 ≤ (2816072795543/12500000000000 : ℝ)^3855 := by
    have hnat : (3080218189 : ℕ)^4879*12500000000000^3855 ≤ 2816072795543^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3080218189 10000000000 2816072795543 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5336361661/10000000000 : ℝ)^4879 ≤ (45164132282361/100000000000000 : ℝ)^3855 := by
    have hnat : (5336361661 : ℕ)^4879*100000000000000^3855 ≤ 45164132282361^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5336361661 10000000000 45164132282361 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(255957611/625000000 : ℝ), (3080218189/10000000000 : ℝ), (5336361661/10000000000 : ℝ)] ![(32307285333509/100000000000000 : ℝ), (2816072795543/12500000000000 : ℝ), (45164132282361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(255957611/625000000 : ℝ)|^4879 ≤ (32307285333509/100000000000000 : ℝ)^3855
        have hw : |(255957611/625000000 : ℝ)|=(255957611/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3080218189/10000000000 : ℝ)|^4879 ≤ (2816072795543/12500000000000 : ℝ)^3855
        have hw : |(3080218189/10000000000 : ℝ)|=(3080218189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5336361661/10000000000 : ℝ)|^4879 ≤ (45164132282361/100000000000000 : ℝ)^3855
        have hw : |(5336361661/10000000000 : ℝ)|=(5336361661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s0_4 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-756389637/5000000000 : ℝ)*x 0 + (4936707513/10000000000 : ℝ)*x 1 + (2887516801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (756389637/5000000000 : ℝ)^4879 ≤ (916009812439/10000000000000 : ℝ)^3855 := by
    have hnat : (756389637 : ℕ)^4879*10000000000000^3855 ≤ 916009812439^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      756389637 5000000000 916009812439 10000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4936707513/10000000000 : ℝ)^4879 ≤ (40926580808847/100000000000000 : ℝ)^3855 := by
    have hnat : (4936707513 : ℕ)^4879*100000000000000^3855 ≤ 40926580808847^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936707513 10000000000 40926580808847 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2887516801/5000000000 : ℝ)^4879 ≤ (24956660527121/50000000000000 : ℝ)^3855 := by
    have hnat : (2887516801 : ℕ)^4879*50000000000000^3855 ≤ 24956660527121^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2887516801 5000000000 24956660527121 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-756389637/5000000000 : ℝ), (4936707513/10000000000 : ℝ), (2887516801/5000000000 : ℝ)] ![(916009812439/10000000000000 : ℝ), (40926580808847/100000000000000 : ℝ), (24956660527121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-756389637/5000000000 : ℝ)|^4879 ≤ (916009812439/10000000000000 : ℝ)^3855
        have hw : |(-756389637/5000000000 : ℝ)|=(756389637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4936707513/10000000000 : ℝ)|^4879 ≤ (40926580808847/100000000000000 : ℝ)^3855
        have hw : |(4936707513/10000000000 : ℝ)|=(4936707513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2887516801/5000000000 : ℝ)|^4879 ≤ (24956660527121/50000000000000 : ℝ)^3855
        have hw : |(2887516801/5000000000 : ℝ)|=(2887516801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s0_5 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2600229989/5000000000 : ℝ)*x 0 + (-1135806309/10000000000 : ℝ)*x 1 + (5775033517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2600229989/5000000000 : ℝ)^4879 ≤ (43713361013337/100000000000000 : ℝ)^3855 := by
    have hnat : (2600229989 : ℕ)^4879*100000000000000^3855 ≤ 43713361013337^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600229989 5000000000 43713361013337 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135806309/10000000000 : ℝ)^4879 ≤ (1593329712119/25000000000000 : ℝ)^3855 := by
    have hnat : (1135806309 : ℕ)^4879*25000000000000^3855 ≤ 1593329712119^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135806309 10000000000 1593329712119 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5775033517/10000000000 : ℝ)^4879 ≤ (24956660062223/50000000000000 : ℝ)^3855 := by
    have hnat : (5775033517 : ℕ)^4879*50000000000000^3855 ≤ 24956660062223^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5775033517 10000000000 24956660062223 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2600229989/5000000000 : ℝ), (-1135806309/10000000000 : ℝ), (5775033517/10000000000 : ℝ)] ![(43713361013337/100000000000000 : ℝ), (1593329712119/25000000000000 : ℝ), (24956660062223/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2600229989/5000000000 : ℝ)|^4879 ≤ (43713361013337/100000000000000 : ℝ)^3855
        have hw : |(2600229989/5000000000 : ℝ)|=(2600229989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135806309/10000000000 : ℝ)|^4879 ≤ (1593329712119/25000000000000 : ℝ)^3855
        have hw : |(-1135806309/10000000000 : ℝ)|=(1135806309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5775033517/10000000000 : ℝ)|^4879 ≤ (24956660062223/50000000000000 : ℝ)^3855
        have hw : |(5775033517/10000000000 : ℝ)|=(5775033517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s0_6 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2600230041/5000000000 : ℝ)*x 0 + (1155006681/2000000000 : ℝ)*x 1 + (-567903163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2600230041/5000000000 : ℝ)^4879 ≤ (21856681059869/50000000000000 : ℝ)^3855 := by
    have hnat : (2600230041 : ℕ)^4879*50000000000000^3855 ≤ 21856681059869^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600230041 5000000000 21856681059869 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155006681/2000000000 : ℝ)^4879 ≤ (9982663779861/20000000000000 : ℝ)^3855 := by
    have hnat : (1155006681 : ℕ)^4879*20000000000000^3855 ≤ 9982663779861^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155006681 2000000000 9982663779861 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567903163/5000000000 : ℝ)^4879 ≤ (6373318969207/100000000000000 : ℝ)^3855 := by
    have hnat : (567903163 : ℕ)^4879*100000000000000^3855 ≤ 6373318969207^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567903163 5000000000 6373318969207 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2600230041/5000000000 : ℝ), (1155006681/2000000000 : ℝ), (-567903163/5000000000 : ℝ)] ![(21856681059869/50000000000000 : ℝ), (9982663779861/20000000000000 : ℝ), (6373318969207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2600230041/5000000000 : ℝ)|^4879 ≤ (21856681059869/50000000000000 : ℝ)^3855
        have hw : |(2600230041/5000000000 : ℝ)|=(2600230041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1155006681/2000000000 : ℝ)|^4879 ≤ (9982663779861/20000000000000 : ℝ)^3855
        have hw : |(1155006681/2000000000 : ℝ)|=(1155006681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567903163/5000000000 : ℝ)|^4879 ≤ (6373318969207/100000000000000 : ℝ)^3855
        have hw : |(-567903163/5000000000 : ℝ)|=(567903163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s0_7 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4101485681/10000000000 : ℝ)*x 0 + (5280097831/10000000000 : ℝ)*x 1 + (627687647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4101485681/10000000000 : ℝ)^4879 ≤ (32368840085237/100000000000000 : ℝ)^3855 := by
    have hnat : (4101485681 : ℕ)^4879*100000000000000^3855 ≤ 32368840085237^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4101485681 10000000000 32368840085237 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5280097831/10000000000 : ℝ)^4879 ≤ (5570287759147/12500000000000 : ℝ)^3855 := by
    have hnat : (5280097831 : ℕ)^4879*12500000000000^3855 ≤ 5570287759147^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280097831 10000000000 5570287759147 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627687647/2000000000 : ℝ)^4879 ≤ (11534428912931/50000000000000 : ℝ)^3855 := by
    have hnat : (627687647 : ℕ)^4879*50000000000000^3855 ≤ 11534428912931^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627687647 2000000000 11534428912931 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4101485681/10000000000 : ℝ), (5280097831/10000000000 : ℝ), (627687647/2000000000 : ℝ)] ![(32368840085237/100000000000000 : ℝ), (5570287759147/12500000000000 : ℝ), (11534428912931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4101485681/10000000000 : ℝ)|^4879 ≤ (32368840085237/100000000000000 : ℝ)^3855
        have hw : |(4101485681/10000000000 : ℝ)|=(4101485681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5280097831/10000000000 : ℝ)|^4879 ≤ (5570287759147/12500000000000 : ℝ)^3855
        have hw : |(5280097831/10000000000 : ℝ)|=(5280097831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627687647/2000000000 : ℝ)|^4879 ≤ (11534428912931/50000000000000 : ℝ)^3855
        have hw : |(627687647/2000000000 : ℝ)|=(627687647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1640_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (4647/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5893/25000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4875/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4875 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4875*1^1024 ≤ 0^1024*1^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4875/1024 : ℝ) ≤ (63750004088234141/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4875 ≤ (63750004088234141/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4875*5000000000000000000^1024 ≤ 63750004088234141^1024*5^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 63750004088234141 5000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (63750004088234141/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4875 := by
      have hnat : (1 : ℕ)^1024*1^4875 ≤ 1^4875*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5063750004088234141/5000000000000000000 : ℝ) ≤ (5013323843674941/5000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (5063750004088234141/5000000000000000000 : ℝ)^1024 ≤ (5013323843674941/5000000000000000 : ℝ)^4875 := by
      have hnat : (5063750004088234141 : ℕ)^1024*5000000000000000^4875 ≤ 5013323843674941^4875*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5063750004088234141 5000000000000000000 5013323843674941 5000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013323843674941/5000000000000000 : ℝ)) (X := (5063750004088234141/5000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2563750004088234141/2500000000000000000 : ℝ) ≤ (2513323843674941/2500000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (2563750004088234141/2500000000000000000 : ℝ)^1024 ≤ (2513323843674941/2500000000000000 : ℝ)^4875 := by
      have hnat : (2563750004088234141 : ℕ)^1024*2500000000000000^4875 ≤ 2513323843674941^4875*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2563750004088234141 2500000000000000000 2513323843674941 2500000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513323843674941/2500000000000000 : ℝ)) (X := (2563750004088234141/2500000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13323843674941/2000000000000000 : ℝ)*(0 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13323843674941/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(63750004088234141/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13323843674941/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4875/1024 : ℝ) := by
    rw [show (1 : ℝ)+(13323843674941/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5013323843674941/5000000000000000 : ℝ) by norm_num, show 1+(63750004088234141/5000000000000000000 : ℝ)+(0 : ℝ)=(5063750004088234141/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(63750004088234141/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13323843674941/2000000000000000 : ℝ)*(2/5 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(13323843674941/2000000000000000 : ℝ)*(2/5 : ℝ)=(2513323843674941/2500000000000000 : ℝ) by norm_num, show 1+2*(63750004088234141/5000000000000000000 : ℝ)=(2563750004088234141/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13323843674941/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13323843674941/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13323843674941/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13323843674941/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13323843674941/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13323843674941/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1510367253/10000000000 : ℝ)*X 0 0+(5797824137/10000000000 : ℝ)*X 0 1+(307167703/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1360380363/2500000000 : ℝ)*X 1 0+(-1996156293/10000000000 : ℝ)*X 1 1+(4914684747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5441523363/10000000000 : ℝ)*X 2 0+(2457341607/5000000000 : ℝ)*X 2 1+(-399231149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((255957611/625000000 : ℝ)*X 0 0+(3080218189/10000000000 : ℝ)*X 0 1+(5336361661/10000000000 : ℝ)*X 0 2+(255957611/625000000 : ℝ)*X 1 0+(3080218189/10000000000 : ℝ)*X 1 1+(5336361661/10000000000 : ℝ)*X 1 2+(255957611/625000000 : ℝ)*X 2 0+(3080218189/10000000000 : ℝ)*X 2 1+(5336361661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-756389637/5000000000 : ℝ)*X 0 0+(4936707513/10000000000 : ℝ)*X 0 1+(2887516801/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2600229989/5000000000 : ℝ)*X 1 0+(-1135806309/10000000000 : ℝ)*X 1 1+(5775033517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2600230041/5000000000 : ℝ)*X 2 0+(1155006681/2000000000 : ℝ)*X 2 1+(-567903163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4101485681/10000000000 : ℝ)*X 0 0+(5280097831/10000000000 : ℝ)*X 0 1+(627687647/2000000000 : ℝ)*X 0 2+(4101485681/10000000000 : ℝ)*X 1 0+(5280097831/10000000000 : ℝ)*X 1 1+(627687647/2000000000 : ℝ)*X 1 2+(4101485681/10000000000 : ℝ)*X 2 0+(5280097831/10000000000 : ℝ)*X 2 1+(627687647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1000681635428784789214689/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1649382659/100000000000000 : ℝ)*(base19) + (495616621/25000000000000 : ℝ)*(base23) + (16140207/12500000000000 : ℝ)*(upper3) + (1098169/3125000000000 : ℝ)*(upper4) + (179888901/50000000000000 : ℝ)*(upper5) + (787790066981619/100000000000000 : ℝ)*(major0) + (787790066981619/100000000000000 : ℝ)*(major1) + (787790066981619/100000000000000 : ℝ)*(major2) + (1132329204246219/100000000000000 : ℝ)*(sp0) + (1132337776037983/100000000000000 : ℝ)*(sp1) + (566168721477079/50000000000000 : ℝ)*(sp2) + (110809362847083/25000000000000 : ℝ)*(sp3) + (5110587211/50000000000000 : ℝ)*(sp4) + (182724607/6250000000000 : ℝ)*(sp7) + (88648074996409/20000000000000 : ℝ)*(f.failure) + (566169712710321/50000000000000 : ℝ)*(f.sum) + (112395488990521/100000000000000000000000000000 : ℝ)*base66 + (2557994476109479/200000000000000000000000000000 : ℝ)*base67 + (912343432309479/200000000000000000000000000000 : ℝ)*base69 + (318467093909479/200000000000000000000000000000 : ℝ)*base71 + (729767217809479/100000000000000000000000000000 : ℝ)*base73 + (128292156690521/200000000000000000000000000000 : ℝ)*base76 + (1431730686309479/200000000000000000000000000000 : ℝ)*base77 + (415177811509479/200000000000000000000000000000 : ℝ)*base79 + (71982451709479/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (48739/80000000000000000000 : ℝ)*base89 + (48739/80000000000000000000 : ℝ)*base91 + (48739/80000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10564632472721248437/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (257717373/12500000000000 : ℝ)*(base19) + (420708657/20000000000000 : ℝ)*(base23) + (2678429/2000000000000 : ℝ)*(base32) + (1322791/400000000000 : ℝ)*(upper3) + (231365421/100000000000000 : ℝ)*(upper5) + (829890102343763/100000000000000 : ℝ)*(major0) + (829890102343763/100000000000000 : ℝ)*(major1) + (829890102343763/100000000000000 : ℝ)*(major2) + (123261829/2000000000000 : ℝ)*(sp1) + (65502679/1000000000000 : ℝ)*(sp2) + (1192852411360737/100000000000000 : ℝ)*(sp4) + (1192844186530303/100000000000000 : ℝ)*(sp5) + (74552734846847/6250000000000 : ℝ)*(sp6) + (11673182681273/2500000000000 : ℝ)*(sp7) + (46692744117237/10000000000000 : ℝ)*(f.failure) + (1192852411360737/100000000000000 : ℝ)*(f.sum) + (7496052542983/100000000000000000000000000000 : ℝ)*base65 + (947367109457017/200000000000000000000000000000 : ℝ)*base68 + (671274964057017/200000000000000000000000000000 : ℝ)*base70 + (734707840057017/200000000000000000000000000000 : ℝ)*base72 + (81239406442983/100000000000000000000000000000 : ℝ)*base73 + (816033789457017/200000000000000000000000000000 : ℝ)*base76 + (699394286057017/200000000000000000000000000000 : ℝ)*base78 + (1382306725257017/200000000000000000000000000000 : ℝ)*base80 + (208529735942983/100000000000000000000000000000 : ℝ)*base81 + (127927/40000000000000000000 : ℝ)*base89 + (127927/40000000000000000000 : ℝ)*base91 + (127927/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1640_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4647/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5893/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1640_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1640_s1_0 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-405109081/2500000000 : ℝ)*x 0 + (5503997163/10000000000 : ℝ)*x 1 + (1284265157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405109081/2500000000 : ℝ)^4879 ≤ (9992801449227/100000000000000 : ℝ)^3855 := by
    have hnat : (405109081 : ℕ)^4879*100000000000000^3855 ≤ 9992801449227^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405109081 2500000000 9992801449227 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503997163/10000000000 : ℝ)^4879 ≤ (4696721378991/10000000000000 : ℝ)^3855 := by
    have hnat : (5503997163 : ℕ)^4879*10000000000000^3855 ≤ 4696721378991^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503997163 10000000000 4696721378991 10000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284265157/2500000000 : ℝ)^4879 ≤ (43039984741563/100000000000000 : ℝ)^3855 := by
    have hnat : (1284265157 : ℕ)^4879*100000000000000^3855 ≤ 43039984741563^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284265157 2500000000 43039984741563 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405109081/2500000000 : ℝ), (5503997163/10000000000 : ℝ), (1284265157/2500000000 : ℝ)] ![(9992801449227/100000000000000 : ℝ), (4696721378991/10000000000000 : ℝ), (43039984741563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405109081/2500000000 : ℝ)|^4879 ≤ (9992801449227/100000000000000 : ℝ)^3855
        have hw : |(-405109081/2500000000 : ℝ)|=(405109081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503997163/10000000000 : ℝ)|^4879 ≤ (4696721378991/10000000000000 : ℝ)^3855
        have hw : |(5503997163/10000000000 : ℝ)|=(5503997163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284265157/2500000000 : ℝ)|^4879 ≤ (43039984741563/100000000000000 : ℝ)^3855
        have hw : |(1284265157/2500000000 : ℝ)|=(1284265157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s1_1 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5363370177/10000000000 : ℝ)*x 0 + (-1811457747/10000000000 : ℝ)*x 1 + (205482417/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363370177/10000000000 : ℝ)^4879 ≤ (9090726253969/20000000000000 : ℝ)^3855 := by
    have hnat : (5363370177 : ℕ)^4879*20000000000000^3855 ≤ 9090726253969^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363370177 10000000000 9090726253969 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1811457747/10000000000 : ℝ)^4879 ≤ (11506386128989/100000000000000 : ℝ)^3855 := by
    have hnat : (1811457747 : ℕ)^4879*100000000000000^3855 ≤ 11506386128989^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811457747 10000000000 11506386128989 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (205482417/400000000 : ℝ)^4879 ≤ (2151999129449/5000000000000 : ℝ)^3855 := by
    have hnat : (205482417 : ℕ)^4879*5000000000000^3855 ≤ 2151999129449^3855*400000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205482417 400000000 2151999129449 5000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363370177/10000000000 : ℝ), (-1811457747/10000000000 : ℝ), (205482417/400000000 : ℝ)] ![(9090726253969/20000000000000 : ℝ), (11506386128989/100000000000000 : ℝ), (2151999129449/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363370177/10000000000 : ℝ)|^4879 ≤ (9090726253969/20000000000000 : ℝ)^3855
        have hw : |(5363370177/10000000000 : ℝ)|=(5363370177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1811457747/10000000000 : ℝ)|^4879 ≤ (11506386128989/100000000000000 : ℝ)^3855
        have hw : |(-1811457747/10000000000 : ℝ)|=(1811457747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(205482417/400000000 : ℝ)|^4879 ≤ (2151999129449/5000000000000 : ℝ)^3855
        have hw : |(205482417/400000000 : ℝ)|=(205482417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s1_2 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681685629/5000000000 : ℝ)*x 0 + (1284264791/2500000000 : ℝ)*x 1 + (-113216123/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681685629/5000000000 : ℝ)^4879 ≤ (45453642864637/100000000000000 : ℝ)^3855 := by
    have hnat : (2681685629 : ℕ)^4879*100000000000000^3855 ≤ 45453642864637^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681685629 5000000000 45453642864637 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1284264791/2500000000 : ℝ)^4879 ≤ (43039969217517/100000000000000 : ℝ)^3855 := by
    have hnat : (1284264791 : ℕ)^4879*100000000000000^3855 ≤ 43039969217517^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284264791 2500000000 43039969217517 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113216123/625000000 : ℝ)^4879 ≤ (1150638790567/10000000000000 : ℝ)^3855 := by
    have hnat : (113216123 : ℕ)^4879*10000000000000^3855 ≤ 1150638790567^3855*625000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113216123 625000000 1150638790567 10000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681685629/5000000000 : ℝ), (1284264791/2500000000 : ℝ), (-113216123/625000000 : ℝ)] ![(45453642864637/100000000000000 : ℝ), (43039969217517/100000000000000 : ℝ), (1150638790567/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681685629/5000000000 : ℝ)|^4879 ≤ (45453642864637/100000000000000 : ℝ)^3855
        have hw : |(2681685629/5000000000 : ℝ)|=(2681685629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1284264791/2500000000 : ℝ)|^4879 ≤ (43039969217517/100000000000000 : ℝ)^3855
        have hw : |(1284264791/2500000000 : ℝ)|=(1284264791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113216123/625000000 : ℝ)|^4879 ≤ (1150638790567/10000000000000 : ℝ)^3855
        have hw : |(-113216123/625000000 : ℝ)|=(113216123/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s1_3 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2090123103/5000000000 : ℝ)*x 0 + (932708421/2500000000 : ℝ)*x 1 + (933648609/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2090123103/5000000000 : ℝ)^4879 ≤ (33157522307221/100000000000000 : ℝ)^3855 := by
    have hnat : (2090123103 : ℕ)^4879*100000000000000^3855 ≤ 33157522307221^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2090123103 5000000000 33157522307221 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (932708421/2500000000 : ℝ)^4879 ≤ (11215667549/39062500000 : ℝ)^3855 := by
    have hnat : (932708421 : ℕ)^4879*39062500000^3855 ≤ 11215667549^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      932708421 2500000000 11215667549 39062500000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (933648609/2000000000 : ℝ)^4879 ≤ (19065184380113/50000000000000 : ℝ)^3855 := by
    have hnat : (933648609 : ℕ)^4879*50000000000000^3855 ≤ 19065184380113^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933648609 2000000000 19065184380113 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2090123103/5000000000 : ℝ), (932708421/2500000000 : ℝ), (933648609/2000000000 : ℝ)] ![(33157522307221/100000000000000 : ℝ), (11215667549/39062500000 : ℝ), (19065184380113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2090123103/5000000000 : ℝ)|^4879 ≤ (33157522307221/100000000000000 : ℝ)^3855
        have hw : |(2090123103/5000000000 : ℝ)|=(2090123103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(932708421/2500000000 : ℝ)|^4879 ≤ (11215667549/39062500000 : ℝ)^3855
        have hw : |(932708421/2500000000 : ℝ)|=(932708421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(933648609/2000000000 : ℝ)|^4879 ≤ (19065184380113/50000000000000 : ℝ)^3855
        have hw : |(933648609/2000000000 : ℝ)|=(933648609/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s1_4 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-810303491/5000000000 : ℝ)*x 0 + (642605543/1250000000 : ℝ)*x 1 + (5500158109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (810303491/5000000000 : ℝ)^4879 ≤ (9994133419249/100000000000000 : ℝ)^3855 := by
    have hnat : (810303491 : ℕ)^4879*100000000000000^3855 ≤ 9994133419249^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      810303491 5000000000 9994133419249 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642605543/1250000000 : ℝ)^4879 ≤ (43080110648321/100000000000000 : ℝ)^3855 := by
    have hnat : (642605543 : ℕ)^4879*100000000000000^3855 ≤ 43080110648321^3855*1250000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642605543 1250000000 43080110648321 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5500158109/10000000000 : ℝ)^4879 ≤ (46925755917399/100000000000000 : ℝ)^3855 := by
    have hnat : (5500158109 : ℕ)^4879*100000000000000^3855 ≤ 46925755917399^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5500158109 10000000000 46925755917399 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-810303491/5000000000 : ℝ), (642605543/1250000000 : ℝ), (5500158109/10000000000 : ℝ)] ![(9994133419249/100000000000000 : ℝ), (43080110648321/100000000000000 : ℝ), (46925755917399/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-810303491/5000000000 : ℝ)|^4879 ≤ (9994133419249/100000000000000 : ℝ)^3855
        have hw : |(-810303491/5000000000 : ℝ)|=(810303491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642605543/1250000000 : ℝ)|^4879 ≤ (43080110648321/100000000000000 : ℝ)^3855
        have hw : |(642605543/1250000000 : ℝ)|=(642605543/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5500158109/10000000000 : ℝ)|^4879 ≤ (46925755917399/100000000000000 : ℝ)^3855
        have hw : |(5500158109/10000000000 : ℝ)|=(5500158109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s1_5 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265366551/10000000000 : ℝ)*x 0 + (-289671931/2000000000 : ℝ)*x 1 + (687519763/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265366551/10000000000 : ℝ)^4879 ≤ (44405008310219/100000000000000 : ℝ)^3855 := by
    have hnat : (5265366551 : ℕ)^4879*100000000000000^3855 ≤ 44405008310219^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265366551 10000000000 44405008310219 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (289671931/2000000000 : ℝ)^4879 ≤ (2167308953059/25000000000000 : ℝ)^3855 := by
    have hnat : (289671931 : ℕ)^4879*25000000000000^3855 ≤ 2167308953059^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289671931 2000000000 2167308953059 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (687519763/1250000000 : ℝ)^4879 ≤ (46925755863409/100000000000000 : ℝ)^3855 := by
    have hnat : (687519763 : ℕ)^4879*100000000000000^3855 ≤ 46925755863409^3855*1250000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687519763 1250000000 46925755863409 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265366551/10000000000 : ℝ), (-289671931/2000000000 : ℝ), (687519763/1250000000 : ℝ)] ![(44405008310219/100000000000000 : ℝ), (2167308953059/25000000000000 : ℝ), (46925755863409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265366551/10000000000 : ℝ)|^4879 ≤ (44405008310219/100000000000000 : ℝ)^3855
        have hw : |(5265366551/10000000000 : ℝ)|=(5265366551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-289671931/2000000000 : ℝ)|^4879 ≤ (2167308953059/25000000000000 : ℝ)^3855
        have hw : |(-289671931/2000000000 : ℝ)|=(289671931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(687519763/1250000000 : ℝ)|^4879 ≤ (46925755863409/100000000000000 : ℝ)^3855
        have hw : |(687519763/1250000000 : ℝ)|=(687519763/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s1_6 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265366417/10000000000 : ℝ)*x 0 + (1375039577/2500000000 : ℝ)*x 1 + (-1448359553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265366417/10000000000 : ℝ)^4879 ≤ (1110125171999/2500000000000 : ℝ)^3855 := by
    have hnat : (5265366417 : ℕ)^4879*2500000000000^3855 ≤ 1110125171999^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265366417 10000000000 1110125171999 2500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1375039577/2500000000 : ℝ)^4879 ≤ (46925758066197/100000000000000 : ℝ)^3855 := by
    have hnat : (1375039577 : ℕ)^4879*100000000000000^3855 ≤ 46925758066197^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1375039577 2500000000 46925758066197 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1448359553/10000000000 : ℝ)^4879 ≤ (541827189971/6250000000000 : ℝ)^3855 := by
    have hnat : (1448359553 : ℕ)^4879*6250000000000^3855 ≤ 541827189971^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1448359553 10000000000 541827189971 6250000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265366417/10000000000 : ℝ), (1375039577/2500000000 : ℝ), (-1448359553/10000000000 : ℝ)] ![(1110125171999/2500000000000 : ℝ), (46925758066197/100000000000000 : ℝ), (541827189971/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265366417/10000000000 : ℝ)|^4879 ≤ (1110125171999/2500000000000 : ℝ)^3855
        have hw : |(5265366417/10000000000 : ℝ)|=(5265366417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1375039577/2500000000 : ℝ)|^4879 ≤ (46925758066197/100000000000000 : ℝ)^3855
        have hw : |(1375039577/2500000000 : ℝ)|=(1375039577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1448359553/10000000000 : ℝ)|^4879 ≤ (541827189971/6250000000000 : ℝ)^3855
        have hw : |(-1448359553/10000000000 : ℝ)|=(1448359553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s1_7 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522584867/1250000000 : ℝ)*x 0 + (116464389/250000000 : ℝ)*x 1 + (1870321003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522584867/1250000000 : ℝ)^4879 ≤ (3316186650531/10000000000000 : ℝ)^3855 := by
    have hnat : (522584867 : ℕ)^4879*10000000000000^3855 ≤ 3316186650531^3855*1250000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522584867 1250000000 3316186650531 10000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116464389/250000000 : ℝ)^4879 ≤ (2376903543079/6250000000000 : ℝ)^3855 := by
    have hnat : (116464389 : ℕ)^4879*6250000000000^3855 ≤ 2376903543079^3855*250000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116464389 250000000 2376903543079 6250000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870321003/5000000000 : ℝ)^4879 ≤ (28807676787879/100000000000000 : ℝ)^3855 := by
    have hnat : (1870321003 : ℕ)^4879*100000000000000^3855 ≤ 28807676787879^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870321003 5000000000 28807676787879 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522584867/1250000000 : ℝ), (116464389/250000000 : ℝ), (1870321003/5000000000 : ℝ)] ![(3316186650531/10000000000000 : ℝ), (2376903543079/6250000000000 : ℝ), (28807676787879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522584867/1250000000 : ℝ)|^4879 ≤ (3316186650531/10000000000000 : ℝ)^3855
        have hw : |(522584867/1250000000 : ℝ)|=(522584867/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116464389/250000000 : ℝ)|^4879 ≤ (2376903543079/6250000000000 : ℝ)^3855
        have hw : |(116464389/250000000 : ℝ)|=(116464389/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1870321003/5000000000 : ℝ)|^4879 ≤ (28807676787879/100000000000000 : ℝ)^3855
        have hw : |(1870321003/5000000000 : ℝ)|=(1870321003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1640_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5893/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4647/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9617/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17407/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5893/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4647/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5893/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4647/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5893/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4647/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5893/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4647/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5893/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4647/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5893/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4647/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4647/100000 : ℝ) ^ (4875/1024 : ℝ) ≤ (11289968283771/25000000000000000000 : ℝ) := by
    have hpowers : (4647/100000 : ℝ)^4875 ≤ (11289968283771/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4647 : ℕ)^4875*25000000000000000000^1024 ≤ 11289968283771^1024*100000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4647 100000 11289968283771 25000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4647/100000 : ℝ)) (X := (11289968283771/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5893/25000 : ℝ) ^ (4875/1024 : ℝ) ≤ (2570876577057777/2500000000000000000 : ℝ) := by
    have hpowers : (5893/25000 : ℝ)^4875 ≤ (2570876577057777/2500000000000000000 : ℝ)^1024 := by
      have hnat : (5893 : ℕ)^4875*2500000000000000000^1024 ≤ 2570876577057777^1024*25000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5893 25000 2570876577057777 2500000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5893/25000 : ℝ)) (X := (2570876577057777/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500011289968283771/12500000000000000000 : ℝ) ≤ (5000000948588587/5000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (12500011289968283771/12500000000000000000 : ℝ)^1024 ≤ (5000000948588587/5000000000000000 : ℝ)^4875 := by
      have hnat : (12500011289968283771 : ℕ)^1024*5000000000000000^4875 ≤ 5000000948588587^4875*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500011289968283771 12500000000000000000 5000000948588587 5000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000948588587/5000000000000000 : ℝ)) (X := (12500011289968283771/12500000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25025720055738861541/25000000000000000000 : ℝ) ≤ (10002160134683171/10000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (25025720055738861541/25000000000000000000 : ℝ)^1024 ≤ (10002160134683171/10000000000000000 : ℝ)^4875 := by
      have hnat : (25025720055738861541 : ℕ)^1024*10000000000000000^4875 ≤ 10002160134683171^4875*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25025720055738861541 25000000000000000000 10002160134683171 10000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002160134683171/10000000000000000 : ℝ)) (X := (25025720055738861541/25000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1252570876577057777/1250000000000000000 : ℝ) ≤ (625269898261823/625000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (1252570876577057777/1250000000000000000 : ℝ)^1024 ≤ (625269898261823/625000000000000 : ℝ)^4875 := by
      have hnat : (1252570876577057777 : ℕ)^1024*625000000000000^4875 ≤ 625269898261823^4875*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1252570876577057777 1250000000000000000 625269898261823 625000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625269898261823/625000000000000 : ℝ)) (X := (1252570876577057777/1250000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(11289968283771/25000000000000000000 : ℝ) ≤ ((23653747155587160229/23656250000000000000 : ℝ)+2*(2158237505997/1892500000000000 : ℝ)*(4647/100000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (23653747155587160229/23656250000000000000 : ℝ)+2*(2158237505997/1892500000000000 : ℝ)*(4647/100000 : ℝ)=(5000000948588587/5000000000000000 : ℝ) by norm_num, show 1+2*(11289968283771/25000000000000000000 : ℝ)=(12500011289968283771/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2570876577057777/2500000000000000000 : ℝ)+(11289968283771/25000000000000000000 : ℝ) ≤ ((23653747155587160229/23656250000000000000 : ℝ)+(2158237505997/1892500000000000 : ℝ)*((5893/25000 : ℝ)+(4647/100000 : ℝ)))^(4875/1024 : ℝ) := by
    rw [show (23653747155587160229/23656250000000000000 : ℝ)+(2158237505997/1892500000000000 : ℝ)*((5893/25000 : ℝ)+(4647/100000 : ℝ))=(10002160134683171/10000000000000000 : ℝ) by norm_num, show 1+(2570876577057777/2500000000000000000 : ℝ)+(11289968283771/25000000000000000000 : ℝ)=(25025720055738861541/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2570876577057777/2500000000000000000 : ℝ) ≤ ((23653747155587160229/23656250000000000000 : ℝ)+2*(2158237505997/1892500000000000 : ℝ)*(5893/25000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (23653747155587160229/23656250000000000000 : ℝ)+2*(2158237505997/1892500000000000 : ℝ)*(5893/25000 : ℝ)=(625269898261823/625000000000000 : ℝ) by norm_num, show 1+2*(2570876577057777/2500000000000000000 : ℝ)=(1252570876577057777/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23653747155587160229/23656250000000000000 : ℝ)*(X 1 0+X 2 0)+(2158237505997/1892500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (4647/100000 : ℝ)) (hi := (5893/25000 : ℝ)) (c := (23653747155587160229/23656250000000000000 : ℝ)) (alpha := (2158237505997/1892500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23653747155587160229/23656250000000000000 : ℝ)*(X 0 1+X 2 1)+(2158237505997/1892500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (4647/100000 : ℝ)) (hi := (5893/25000 : ℝ)) (c := (23653747155587160229/23656250000000000000 : ℝ)) (alpha := (2158237505997/1892500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23653747155587160229/23656250000000000000 : ℝ)*(X 0 2+X 1 2)+(2158237505997/1892500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (4647/100000 : ℝ)) (hi := (5893/25000 : ℝ)) (c := (23653747155587160229/23656250000000000000 : ℝ)) (alpha := (2158237505997/1892500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-405109081/2500000000 : ℝ)*X 0 0+(5503997163/10000000000 : ℝ)*X 0 1+(1284265157/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5363370177/10000000000 : ℝ)*X 1 0+(-1811457747/10000000000 : ℝ)*X 1 1+(205482417/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2681685629/5000000000 : ℝ)*X 2 0+(1284264791/2500000000 : ℝ)*X 2 1+(-113216123/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2090123103/5000000000 : ℝ)*X 0 0+(932708421/2500000000 : ℝ)*X 0 1+(933648609/2000000000 : ℝ)*X 0 2+(2090123103/5000000000 : ℝ)*X 1 0+(932708421/2500000000 : ℝ)*X 1 1+(933648609/2000000000 : ℝ)*X 1 2+(2090123103/5000000000 : ℝ)*X 2 0+(932708421/2500000000 : ℝ)*X 2 1+(933648609/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-810303491/5000000000 : ℝ)*X 0 0+(642605543/1250000000 : ℝ)*X 0 1+(5500158109/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5265366551/10000000000 : ℝ)*X 1 0+(-289671931/2000000000 : ℝ)*X 1 1+(687519763/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265366417/10000000000 : ℝ)*X 2 0+(1375039577/2500000000 : ℝ)*X 2 1+(-1448359553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((522584867/1250000000 : ℝ)*X 0 0+(116464389/250000000 : ℝ)*X 0 1+(1870321003/5000000000 : ℝ)*X 0 2+(522584867/1250000000 : ℝ)*X 1 0+(116464389/250000000 : ℝ)*X 1 1+(1870321003/5000000000 : ℝ)*X 1 2+(522584867/1250000000 : ℝ)*X 2 0+(116464389/250000000 : ℝ)*X 2 1+(1870321003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1919447583800250473344741137/591406250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49555887/50000000000000 : ℝ)*(base1) + (218462921/100000000000000 : ℝ)*(base19) + (43896141/5000000000000 : ℝ)*(base23) + (6303137/6250000000000 : ℝ)*(lower2) + (19992737/12500000000000 : ℝ)*(lower4) + (8771551/20000000000000 : ℝ)*(upper5) + (948009095195899/50000000000000 : ℝ)*(major0) + (948009095195899/50000000000000 : ℝ)*(major1) + (948009095195899/50000000000000 : ℝ)*(major2) + (1362632548674983/50000000000000 : ℝ)*(sp0) + (340658097471909/12500000000000 : ℝ)*(sp1) + (681316030078843/25000000000000 : ℝ)*(sp2) + (1066770399410201/100000000000000 : ℝ)*(sp3) + (193959477/25000000000000 : ℝ)*(sp7) + (533385637179941/50000000000000 : ℝ)*(f.failure) + (170329062389887/6250000000000 : ℝ)*(f.sum) + (193343856465143/11828125000000000000000000000 : ℝ)*base66 + (15724657517476113371/1182812500000000000000000000000000 : ℝ)*base67 + (402185092341074129/1182812500000000000000000000000000 : ℝ)*base70 + (4556741768863613371/1182812500000000000000000000000000 : ℝ)*base71 + (318425875277553/47312500000000000000000000000 : ℝ)*base73 + (3606509260566074129/1182812500000000000000000000000000 : ℝ)*base76 + (12276350006638613371/1182812500000000000000000000000000 : ℝ)*base77 + (17356320688804238371/1182812500000000000000000000000000 : ℝ)*base79 + (42468185078519/94625000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1672889/200000000000000000000 : ℝ)*base90 + (1672889/200000000000000000000 : ℝ)*base92 + (1672889/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3491217583448155487085737733/1182812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (162397017/25000000000000 : ℝ)*(base19) + (26220291/4000000000000 : ℝ)*(base23) + (7685429/25000000000000 : ℝ)*(upper2) + (36662241/50000000000000 : ℝ)*(upper3) + (4307419/5000000000000 : ℝ)*(upper5) + (1936242985683159/100000000000000 : ℝ)*(major0) + (1936242985683159/100000000000000 : ℝ)*(major1) + (1936242985683159/100000000000000 : ℝ)*(major2) + (1198511309/20000000000000 : ℝ)*(sp1) + (3489495399/50000000000000 : ℝ)*(sp2) + (347885326643751/12500000000000 : ℝ)*(sp4) + (695768992751349/25000000000000 : ℝ)*(sp5) + (86971093082873/3125000000000 : ℝ)*(sp6) + (544701629914421/50000000000000 : ℝ)*(sp7) + (544701629914421/50000000000000 : ℝ)*(f.failure) + (347885326643751/12500000000000 : ℝ)*(f.sum) + (326114553680523/94625000000000000000000000000 : ℝ)*base65 + (10920920176033579089/2365625000000000000000000000000000 : ℝ)*base68 + (3024212922203920911/2365625000000000000000000000000000 : ℝ)*base69 + (11497383958086704089/2365625000000000000000000000000000 : ℝ)*base72 + (8899773331949/47312500000000000000000000000 : ℝ)*base73 + (4538089185011704089/2365625000000000000000000000000000 : ℝ)*base76 + (2527051139321079089/2365625000000000000000000000000000 : ℝ)*base78 + (2993916940041420911/2365625000000000000000000000000000 : ℝ)*base79 + (343554156547023/94625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (860809/200000000000000000000 : ℝ)*base90 + (860809/200000000000000000000 : ℝ)*base92 + (860809/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1640_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5893/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4647/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9617/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17407/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1640_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1640_s2_0 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1630734687/10000000000 : ℝ)*x 0 + (109094597/200000000 : ℝ)*x 1 + (5179546479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1630734687/10000000000 : ℝ)^4879 ≤ (2014649168297/20000000000000 : ℝ)^3855 := by
    have hnat : (1630734687 : ℕ)^4879*20000000000000^3855 ≤ 2014649168297^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1630734687 10000000000 2014649168297 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109094597/200000000 : ℝ)^4879 ≤ (4643576165689/10000000000000 : ℝ)^3855 := by
    have hnat : (109094597 : ℕ)^4879*10000000000000^3855 ≤ 4643576165689^3855*200000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109094597 200000000 4643576165689 10000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179546479/10000000000 : ℝ)^4879 ≤ (4349099248337/10000000000000 : ℝ)^3855 := by
    have hnat : (5179546479 : ℕ)^4879*10000000000000^3855 ≤ 4349099248337^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179546479 10000000000 4349099248337 10000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1630734687/10000000000 : ℝ), (109094597/200000000 : ℝ), (5179546479/10000000000 : ℝ)] ![(2014649168297/20000000000000 : ℝ), (4643576165689/10000000000000 : ℝ), (4349099248337/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1630734687/10000000000 : ℝ)|^4879 ≤ (2014649168297/20000000000000 : ℝ)^3855
        have hw : |(-1630734687/10000000000 : ℝ)|=(1630734687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109094597/200000000 : ℝ)|^4879 ≤ (4643576165689/10000000000000 : ℝ)^3855
        have hw : |(109094597/200000000 : ℝ)|=(109094597/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179546479/10000000000 : ℝ)|^4879 ≤ (4349099248337/10000000000000 : ℝ)^3855
        have hw : |(5179546479/10000000000 : ℝ)|=(5179546479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s2_1 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337593919/2500000000 : ℝ)*x 0 + (-110786013/625000000 : ℝ)*x 1 + (2589773609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337593919/2500000000 : ℝ)^4879 ≤ (45314297303889/100000000000000 : ℝ)^3855 := by
    have hnat : (1337593919 : ℕ)^4879*100000000000000^3855 ≤ 45314297303889^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337593919 2500000000 45314297303889 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (110786013/625000000 : ℝ)^4879 ≤ (2798675588559/25000000000000 : ℝ)^3855 := by
    have hnat : (110786013 : ℕ)^4879*25000000000000^3855 ≤ 2798675588559^3855*625000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110786013 625000000 2798675588559 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589773609/5000000000 : ℝ)^4879 ≤ (43491000336783/100000000000000 : ℝ)^3855 := by
    have hnat : (2589773609 : ℕ)^4879*100000000000000^3855 ≤ 43491000336783^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589773609 5000000000 43491000336783 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337593919/2500000000 : ℝ), (-110786013/625000000 : ℝ), (2589773609/5000000000 : ℝ)] ![(45314297303889/100000000000000 : ℝ), (2798675588559/25000000000000 : ℝ), (43491000336783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337593919/2500000000 : ℝ)|^4879 ≤ (45314297303889/100000000000000 : ℝ)^3855
        have hw : |(1337593919/2500000000 : ℝ)|=(1337593919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-110786013/625000000 : ℝ)|^4879 ≤ (2798675588559/25000000000000 : ℝ)^3855
        have hw : |(-110786013/625000000 : ℝ)|=(110786013/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589773609/5000000000 : ℝ)|^4879 ≤ (43491000336783/100000000000000 : ℝ)^3855
        have hw : |(2589773609/5000000000 : ℝ)|=(2589773609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s2_2 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107007561/200000000 : ℝ)*x 0 + (2589772929/5000000000 : ℝ)*x 1 + (-110785927/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107007561/200000000 : ℝ)^4879 ≤ (45314322750981/100000000000000 : ℝ)^3855 := by
    have hnat : (107007561 : ℕ)^4879*100000000000000^3855 ≤ 45314322750981^3855*200000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107007561 200000000 45314322750981 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589772929/5000000000 : ℝ)^4879 ≤ (2718186617747/6250000000000 : ℝ)^3855 := by
    have hnat : (2589772929 : ℕ)^4879*6250000000000^3855 ≤ 2718186617747^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589772929 5000000000 2718186617747 6250000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (110785927/625000000 : ℝ)^4879 ≤ (11194691355761/100000000000000 : ℝ)^3855 := by
    have hnat : (110785927 : ℕ)^4879*100000000000000^3855 ≤ 11194691355761^3855*625000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      110785927 625000000 11194691355761 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107007561/200000000 : ℝ), (2589772929/5000000000 : ℝ), (-110785927/625000000 : ℝ)] ![(45314322750981/100000000000000 : ℝ), (2718186617747/6250000000000 : ℝ), (11194691355761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107007561/200000000 : ℝ)|^4879 ≤ (45314322750981/100000000000000 : ℝ)^3855
        have hw : |(107007561/200000000 : ℝ)|=(107007561/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589772929/5000000000 : ℝ)|^4879 ≤ (2718186617747/6250000000000 : ℝ)^3855
        have hw : |(2589772929/5000000000 : ℝ)|=(2589772929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-110785927/625000000 : ℝ)|^4879 ≤ (11194691355761/100000000000000 : ℝ)^3855
        have hw : |(-110785927/625000000 : ℝ)|=(110785927/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s2_3 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (837580847/2000000000 : ℝ)*x 0 + (3847255167/10000000000 : ℝ)*x 1 + (910052581/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (837580847/2000000000 : ℝ)^4879 ≤ (8308604820729/25000000000000 : ℝ)^3855 := by
    have hnat : (837580847 : ℕ)^4879*25000000000000^3855 ≤ 8308604820729^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      837580847 2000000000 8308604820729 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3847255167/10000000000 : ℝ)^4879 ≤ (14925367955849/50000000000000 : ℝ)^3855 := by
    have hnat : (3847255167 : ℕ)^4879*50000000000000^3855 ≤ 14925367955849^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3847255167 10000000000 14925367955849 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910052581/2000000000 : ℝ)^4879 ≤ (2307177798923/6250000000000 : ℝ)^3855 := by
    have hnat : (910052581 : ℕ)^4879*6250000000000^3855 ≤ 2307177798923^3855*2000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910052581 2000000000 2307177798923 6250000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(837580847/2000000000 : ℝ), (3847255167/10000000000 : ℝ), (910052581/2000000000 : ℝ)] ![(8308604820729/25000000000000 : ℝ), (14925367955849/50000000000000 : ℝ), (2307177798923/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(837580847/2000000000 : ℝ)|^4879 ≤ (8308604820729/25000000000000 : ℝ)^3855
        have hw : |(837580847/2000000000 : ℝ)|=(837580847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3847255167/10000000000 : ℝ)|^4879 ≤ (14925367955849/50000000000000 : ℝ)^3855
        have hw : |(3847255167/10000000000 : ℝ)|=(3847255167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(910052581/2000000000 : ℝ)|^4879 ≤ (2307177798923/6250000000000 : ℝ)^3855
        have hw : |(910052581/2000000000 : ℝ)|=(910052581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s2_4 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1630805487/10000000000 : ℝ)*x 0 + (5181681581/10000000000 : ℝ)*x 1 + (340785769/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1630805487/10000000000 : ℝ)^4879 ≤ (5036899677559/50000000000000 : ℝ)^3855 := by
    have hnat : (1630805487 : ℕ)^4879*50000000000000^3855 ≤ 5036899677559^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1630805487 10000000000 5036899677559 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181681581/10000000000 : ℝ)^4879 ≤ (4351368362889/10000000000000 : ℝ)^3855 := by
    have hnat : (5181681581 : ℕ)^4879*10000000000000^3855 ≤ 4351368362889^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181681581 10000000000 4351368362889 10000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340785769/625000000 : ℝ)^4879 ≤ (11603129251757/25000000000000 : ℝ)^3855 := by
    have hnat : (340785769 : ℕ)^4879*25000000000000^3855 ≤ 11603129251757^3855*625000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340785769 625000000 11603129251757 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1630805487/10000000000 : ℝ), (5181681581/10000000000 : ℝ), (340785769/625000000 : ℝ)] ![(5036899677559/50000000000000 : ℝ), (4351368362889/10000000000000 : ℝ), (11603129251757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1630805487/10000000000 : ℝ)|^4879 ≤ (5036899677559/50000000000000 : ℝ)^3855
        have hw : |(-1630805487/10000000000 : ℝ)|=(1630805487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181681581/10000000000 : ℝ)|^4879 ≤ (4351368362889/10000000000000 : ℝ)^3855
        have hw : |(5181681581/10000000000 : ℝ)|=(5181681581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340785769/625000000 : ℝ)|^4879 ≤ (11603129251757/25000000000000 : ℝ)^3855
        have hw : |(340785769/625000000 : ℝ)|=(340785769/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s2_5 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276947439/10000000000 : ℝ)*x 0 + (-374887297/2500000000 : ℝ)*x 1 + (109051451/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276947439/10000000000 : ℝ)^4879 ≤ (5566081730059/12500000000000 : ℝ)^3855 := by
    have hnat : (5276947439 : ℕ)^4879*12500000000000^3855 ≤ 5566081730059^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276947439 10000000000 5566081730059 12500000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374887297/2500000000 : ℝ)^4879 ≤ (1811765297209/20000000000000 : ℝ)^3855 := by
    have hnat : (374887297 : ℕ)^4879*20000000000000^3855 ≤ 1811765297209^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374887297 2500000000 1811765297209 20000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109051451/200000000 : ℝ)^4879 ≤ (46412519657207/100000000000000 : ℝ)^3855 := by
    have hnat : (109051451 : ℕ)^4879*100000000000000^3855 ≤ 46412519657207^3855*200000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109051451 200000000 46412519657207 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276947439/10000000000 : ℝ), (-374887297/2500000000 : ℝ), (109051451/200000000 : ℝ)] ![(5566081730059/12500000000000 : ℝ), (1811765297209/20000000000000 : ℝ), (46412519657207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276947439/10000000000 : ℝ)|^4879 ≤ (5566081730059/12500000000000 : ℝ)^3855
        have hw : |(5276947439/10000000000 : ℝ)|=(5276947439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-374887297/2500000000 : ℝ)|^4879 ≤ (1811765297209/20000000000000 : ℝ)^3855
        have hw : |(-374887297/2500000000 : ℝ)|=(374887297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109051451/200000000 : ℝ)|^4879 ≤ (46412519657207/100000000000000 : ℝ)^3855
        have hw : |(109051451/200000000 : ℝ)|=(109051451/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s2_6 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638474171/5000000000 : ℝ)*x 0 + (5452571769/10000000000 : ℝ)*x 1 + (-1499549027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638474171/5000000000 : ℝ)^4879 ≤ (22264331742167/50000000000000 : ℝ)^3855 := by
    have hnat : (2638474171 : ℕ)^4879*50000000000000^3855 ≤ 22264331742167^3855*5000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638474171 5000000000 22264331742167 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452571769/10000000000 : ℝ)^4879 ≤ (46412511243427/100000000000000 : ℝ)^3855 := by
    have hnat : (5452571769 : ℕ)^4879*100000000000000^3855 ≤ 46412511243427^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452571769 10000000000 46412511243427 100000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1499549027/10000000000 : ℝ)^4879 ≤ (4529412627543/50000000000000 : ℝ)^3855 := by
    have hnat : (1499549027 : ℕ)^4879*50000000000000^3855 ≤ 4529412627543^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499549027 10000000000 4529412627543 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638474171/5000000000 : ℝ), (5452571769/10000000000 : ℝ), (-1499549027/10000000000 : ℝ)] ![(22264331742167/50000000000000 : ℝ), (46412511243427/100000000000000 : ℝ), (4529412627543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638474171/5000000000 : ℝ)|^4879 ≤ (22264331742167/50000000000000 : ℝ)^3855
        have hw : |(2638474171/5000000000 : ℝ)|=(2638474171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452571769/10000000000 : ℝ)|^4879 ≤ (46412511243427/100000000000000 : ℝ)^3855
        have hw : |(5452571769/10000000000 : ℝ)|=(5452571769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1499549027/10000000000 : ℝ)|^4879 ≤ (4529412627543/50000000000000 : ℝ)^3855
        have hw : |(-1499549027/10000000000 : ℝ)|=(1499549027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1640_s2_7 (p : ℝ) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1047021797/2500000000 : ℝ)*x 0 + (4544810737/10000000000 : ℝ)*x 1 + (3852766809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047021797/2500000000 : ℝ)^4879 ≤ (16618128417893/50000000000000 : ℝ)^3855 := by
    have hnat : (1047021797 : ℕ)^4879*50000000000000^3855 ≤ 16618128417893^3855*2500000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047021797 2500000000 16618128417893 50000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4544810737/10000000000 : ℝ)^4879 ≤ (3685887274963/10000000000000 : ℝ)^3855 := by
    have hnat : (4544810737 : ℕ)^4879*10000000000000^3855 ≤ 3685887274963^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4544810737 10000000000 3685887274963 10000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3852766809/10000000000 : ℝ)^4879 ≤ (7476217601517/25000000000000 : ℝ)^3855 := by
    have hnat : (3852766809 : ℕ)^4879*25000000000000^3855 ≤ 7476217601517^3855*10000000000^4879 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3852766809 10000000000 7476217601517 25000000000000 4879 3855 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4879/1024 : ℝ)) 4879 3855 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047021797/2500000000 : ℝ), (4544810737/10000000000 : ℝ), (3852766809/10000000000 : ℝ)] ![(16618128417893/50000000000000 : ℝ), (3685887274963/10000000000000 : ℝ), (7476217601517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047021797/2500000000 : ℝ)|^4879 ≤ (16618128417893/50000000000000 : ℝ)^3855
        have hw : |(1047021797/2500000000 : ℝ)|=(1047021797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4544810737/10000000000 : ℝ)|^4879 ≤ (3685887274963/10000000000000 : ℝ)^3855
        have hw : |(4544810737/10000000000 : ℝ)|=(4544810737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3852766809/10000000000 : ℝ)|^4879 ≤ (7476217601517/25000000000000 : ℝ)^3855
        have hw : |(3852766809/10000000000 : ℝ)|=(3852766809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1640_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17407/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5267/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16379/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17407/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17407/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9617/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17407/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17407/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9617/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17407/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17407/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9617/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9617/100000 : ℝ) ^ (4875/1024 : ℝ) ≤ (1440501772797339/100000000000000000000 : ℝ) := by
    have hpowers : (9617/100000 : ℝ)^4875 ≤ (1440501772797339/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9617 : ℕ)^4875*100000000000000000000^1024 ≤ 1440501772797339^1024*100000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9617 100000 1440501772797339 100000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9617/100000 : ℝ)) (X := (1440501772797339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17407/100000 : ℝ) ^ (4875/1024 : ℝ) ≤ (24281883904440699/100000000000000000000 : ℝ) := by
    have hpowers : (17407/100000 : ℝ)^4875 ≤ (24281883904440699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17407 : ℕ)^4875*100000000000000000000^1024 ≤ 24281883904440699^1024*100000^4875 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17407 100000 24281883904440699 100000000000000000000 4875 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17407/100000 : ℝ)) (X := (24281883904440699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001440501772797339/50000000000000000000 : ℝ) ≤ (312501891098757/312500000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (50001440501772797339/50000000000000000000 : ℝ)^1024 ≤ (312501891098757/312500000000000 : ℝ)^4875 := by
      have hnat : (50001440501772797339 : ℕ)^1024*312500000000000^4875 ≤ 312501891098757^4875*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001440501772797339 50000000000000000000 312501891098757 312500000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312501891098757/312500000000000 : ℝ)) (X := (50001440501772797339/50000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012861192838619019/50000000000000000000 : ℝ) ≤ (2000108049424869/2000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (50012861192838619019/50000000000000000000 : ℝ)^1024 ≤ (2000108049424869/2000000000000000 : ℝ)^4875 := by
      have hnat : (50012861192838619019 : ℕ)^1024*2000000000000000^4875 ≤ 2000108049424869^4875*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012861192838619019 50000000000000000000 2000108049424869 2000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000108049424869/2000000000000000 : ℝ)) (X := (50012861192838619019/50000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024281883904440699/50000000000000000000 : ℝ) ≤ (5000509989544233/5000000000000000 : ℝ) ^ (4875/1024 : ℝ) := by
    have hpowers : (50024281883904440699/50000000000000000000 : ℝ)^1024 ≤ (5000509989544233/5000000000000000 : ℝ)^4875 := by
      have hnat : (50024281883904440699 : ℕ)^1024*5000000000000000^4875 ≤ 5000509989544233^4875*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024281883904440699 50000000000000000000 5000509989544233 5000000000000000 1024 4875 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000509989544233/5000000000000000 : ℝ)) (X := (50024281883904440699/50000000000000000000 : ℝ)) (by norm_num) 4875 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1440501772797339/100000000000000000000 : ℝ) ≤ ((38945622124250120823/38950000000000000000 : ℝ)+2*(479731964121/779000000000000 : ℝ)*(9617/100000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (38945622124250120823/38950000000000000000 : ℝ)+2*(479731964121/779000000000000 : ℝ)*(9617/100000 : ℝ)=(312501891098757/312500000000000 : ℝ) by norm_num, show 1+2*(1440501772797339/100000000000000000000 : ℝ)=(50001440501772797339/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24281883904440699/100000000000000000000 : ℝ)+(1440501772797339/100000000000000000000 : ℝ) ≤ ((38945622124250120823/38950000000000000000 : ℝ)+(479731964121/779000000000000 : ℝ)*((17407/100000 : ℝ)+(9617/100000 : ℝ)))^(4875/1024 : ℝ) := by
    rw [show (38945622124250120823/38950000000000000000 : ℝ)+(479731964121/779000000000000 : ℝ)*((17407/100000 : ℝ)+(9617/100000 : ℝ))=(2000108049424869/2000000000000000 : ℝ) by norm_num, show 1+(24281883904440699/100000000000000000000 : ℝ)+(1440501772797339/100000000000000000000 : ℝ)=(50012861192838619019/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24281883904440699/100000000000000000000 : ℝ) ≤ ((38945622124250120823/38950000000000000000 : ℝ)+2*(479731964121/779000000000000 : ℝ)*(17407/100000 : ℝ))^(4875/1024 : ℝ) := by
    rw [show (38945622124250120823/38950000000000000000 : ℝ)+2*(479731964121/779000000000000 : ℝ)*(17407/100000 : ℝ)=(5000509989544233/5000000000000000 : ℝ) by norm_num, show 1+2*(24281883904440699/100000000000000000000 : ℝ)=(50024281883904440699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38945622124250120823/38950000000000000000 : ℝ)*(X 1 0+X 2 0)+(479731964121/779000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (9617/100000 : ℝ)) (hi := (17407/100000 : ℝ)) (c := (38945622124250120823/38950000000000000000 : ℝ)) (alpha := (479731964121/779000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38945622124250120823/38950000000000000000 : ℝ)*(X 0 1+X 2 1)+(479731964121/779000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (9617/100000 : ℝ)) (hi := (17407/100000 : ℝ)) (c := (38945622124250120823/38950000000000000000 : ℝ)) (alpha := (479731964121/779000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38945622124250120823/38950000000000000000 : ℝ)*(X 0 2+X 1 2)+(479731964121/779000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4875/1024 : ℝ)) (lo := (9617/100000 : ℝ)) (hi := (17407/100000 : ℝ)) (c := (38945622124250120823/38950000000000000000 : ℝ)) (alpha := (479731964121/779000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1630734687/10000000000 : ℝ)*X 0 0+(109094597/200000000 : ℝ)*X 0 1+(5179546479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337593919/2500000000 : ℝ)*X 1 0+(-110786013/625000000 : ℝ)*X 1 1+(2589773609/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((107007561/200000000 : ℝ)*X 2 0+(2589772929/5000000000 : ℝ)*X 2 1+(-110785927/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((837580847/2000000000 : ℝ)*X 0 0+(3847255167/10000000000 : ℝ)*X 0 1+(910052581/2000000000 : ℝ)*X 0 2+(837580847/2000000000 : ℝ)*X 1 0+(3847255167/10000000000 : ℝ)*X 1 1+(910052581/2000000000 : ℝ)*X 1 2+(837580847/2000000000 : ℝ)*X 2 0+(3847255167/10000000000 : ℝ)*X 2 1+(910052581/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1630805487/10000000000 : ℝ)*X 0 0+(5181681581/10000000000 : ℝ)*X 0 1+(340785769/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276947439/10000000000 : ℝ)*X 1 0+(-374887297/2500000000 : ℝ)*X 1 1+(109051451/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638474171/5000000000 : ℝ)*X 2 0+(5452571769/10000000000 : ℝ)*X 2 1+(-1499549027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1047021797/2500000000 : ℝ)*X 0 0+(4544810737/10000000000 : ℝ)*X 0 1+(3852766809/10000000000 : ℝ)*X 0 2+(1047021797/2500000000 : ℝ)*X 1 0+(4544810737/10000000000 : ℝ)*X 1 1+(3852766809/10000000000 : ℝ)*X 1 2+(1047021797/2500000000 : ℝ)*X 2 0+(4544810737/10000000000 : ℝ)*X 2 1+(3852766809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1640_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15156717141980249347462390653/1947500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14015397/5000000000000 : ℝ)*(base19) + (239375329/12500000000000 : ℝ)*(base23) + (10045349/12500000000000 : ℝ)*(upper4) + (99599893/20000000000000 : ℝ)*(upper5) + (2528224864835131/100000000000000 : ℝ)*(major0) + (2528224864835131/100000000000000 : ℝ)*(major1) + (632056216208783/25000000000000 : ℝ)*(major2) + (145357901889907/4000000000000 : ℝ)*(sp0) + (3633962052033611/100000000000000 : ℝ)*(sp1) + (3633972984803467/100000000000000 : ℝ)*(sp2) + (355616829623097/25000000000000 : ℝ)*(sp3) + (3419069803/12500000000000 : ℝ)*(sp4) + (12567464547/100000000000000 : ℝ)*(sp5) + (7251949993/100000000000000 : ℝ)*(sp7) + (711237285221191/50000000000000 : ℝ)*(f.failure) + (3633974899806099/100000000000000 : ℝ)*(f.sum) + (73140677620923/77900000000000000000000000000 : ℝ)*base65 + (270583546759401727/205000000000000000000000000000000 : ℝ)*base67 + (10936228603251925909/973750000000000000000000000000000 : ℝ)*base69 + (255246819849401727/205000000000000000000000000000000 : ℝ)*base71 + (46771444891123/77900000000000000000000000000 : ℝ)*base73 + (24825356689210675909/973750000000000000000000000000000 : ℝ)*base75 + (9667545613937582813/3895000000000000000000000000000000 : ℝ)*base77 + (23749143805617417187/3895000000000000000000000000000000 : ℝ)*base80 + (26268547294501/38950000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1880861/200000000000000000000 : ℝ)*base89 + (1880861/200000000000000000000 : ℝ)*base91 + (119139/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9768373777504448886233937531/1947500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (201694573/100000000000000 : ℝ)*(base19) + (133748153/10000000000000 : ℝ)*(base23) + (3178197/1562500000000 : ℝ)*(lower4) + (15011487/50000000000000 : ℝ)*(lower5) + (2568263151990627/100000000000000 : ℝ)*(major0) + (2568263151990627/100000000000000 : ℝ)*(major1) + (642065787997657/25000000000000 : ℝ)*(major2) + (1337096787/20000000000000 : ℝ)*(sp1) + (152104631/1000000000000 : ℝ)*(sp2) + (620257791/20000000000000 : ℝ)*(sp3) + (922881129344879/25000000000000 : ℝ)*(sp4) + (230719851887563/6250000000000 : ℝ)*(sp5) + (1845753984717443/50000000000000 : ℝ)*(sp6) + (180624814764709/12500000000000 : ℝ)*(sp7) + (722500809703313/50000000000000 : ℝ)*(f.failure) + (922881129344879/25000000000000 : ℝ)*(f.sum) + (17886934523351/15580000000000000000000000000 : ℝ)*base65 + (16324866802837926021/3895000000000000000000000000000000 : ℝ)*base67 + (122979545892024371/23750000000000000000000000000000 : ℝ)*base69 + (19718196496422073979/3895000000000000000000000000000000 : ℝ)*base72 + (45622165471671/15580000000000000000000000000 : ℝ)*base73 + (167687772199524371/23750000000000000000000000000000 : ℝ)*base75 + (29853721658428123979/3895000000000000000000000000000000 : ℝ)*base78 + (21520653921878123979/3895000000000000000000000000000000 : ℝ)*base80 + (82741071555083/38950000000000000000000000000 : ℝ)*base82 + (1953877/200000000000000000000 : ℝ)*base90 + (1953877/200000000000000000000 : ℝ)*base92 + (3953877/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1640_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17407/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9617/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16379/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1640_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1640_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16379/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1640_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1640_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1640_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4875/1024 : ℝ) ≤ p) (hpb : p ≤ (4879/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7109371/4000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16379/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1640_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
