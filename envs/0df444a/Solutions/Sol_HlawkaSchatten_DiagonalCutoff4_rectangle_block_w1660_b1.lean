-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1660_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:21.866017+00:00
-- url     : https://prove2.me/submissions/9ef43d54-b06b-4cd0-9be3-5c5517268e0c

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
theorem support_rectangle_w1660_s3_0 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-793026581/5000000000 : ℝ)*x 0 + (5444641339/10000000000 : ℝ)*x 1 + (5184478757/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (793026581/5000000000 : ℝ)^4959 ≤ (4911198143549/50000000000000 : ℝ)^3935 := by
    have hnat : (793026581 : ℕ)^4959*50000000000000^3935 ≤ 4911198143549^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      793026581 5000000000 4911198143549 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444641339/10000000000 : ℝ)^4959 ≤ (23239720694783/50000000000000 : ℝ)^3935 := by
    have hnat : (5444641339 : ℕ)^4959*50000000000000^3935 ≤ 23239720694783^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444641339 10000000000 23239720694783 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184478757/10000000000 : ℝ)^4959 ≤ (10924540577553/25000000000000 : ℝ)^3935 := by
    have hnat : (5184478757 : ℕ)^4959*25000000000000^3935 ≤ 10924540577553^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184478757 10000000000 10924540577553 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-793026581/5000000000 : ℝ), (5444641339/10000000000 : ℝ), (5184478757/10000000000 : ℝ)] ![(4911198143549/50000000000000 : ℝ), (23239720694783/50000000000000 : ℝ), (10924540577553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-793026581/5000000000 : ℝ)|^4959 ≤ (4911198143549/50000000000000 : ℝ)^3935
        have hw : |(-793026581/5000000000 : ℝ)|=(793026581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444641339/10000000000 : ℝ)|^4959 ≤ (23239720694783/50000000000000 : ℝ)^3935
        have hw : |(5444641339/10000000000 : ℝ)|=(5444641339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184478757/10000000000 : ℝ)|^4959 ≤ (10924540577553/25000000000000 : ℝ)^3935
        have hw : |(5184478757/10000000000 : ℝ)|=(5184478757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s3_1 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069248363/2000000000 : ℝ)*x 0 + (-343986239/2000000000 : ℝ)*x 1 + (5184478641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069248363/2000000000 : ℝ)^4959 ≤ (45423336777777/100000000000000 : ℝ)^3935 := by
    have hnat : (1069248363 : ℕ)^4959*100000000000000^3935 ≤ 45423336777777^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069248363 2000000000 45423336777777 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (343986239/2000000000 : ℝ)^4959 ≤ (2175700426901/20000000000000 : ℝ)^3935 := by
    have hnat : (343986239 : ℕ)^4959*20000000000000^3935 ≤ 2175700426901^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343986239 2000000000 2175700426901 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5184478641/10000000000 : ℝ)^4959 ≤ (5462270134757/12500000000000 : ℝ)^3935 := by
    have hnat : (5184478641 : ℕ)^4959*12500000000000^3935 ≤ 5462270134757^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184478641 10000000000 5462270134757 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069248363/2000000000 : ℝ), (-343986239/2000000000 : ℝ), (5184478641/10000000000 : ℝ)] ![(45423336777777/100000000000000 : ℝ), (2175700426901/20000000000000 : ℝ), (5462270134757/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069248363/2000000000 : ℝ)|^4959 ≤ (45423336777777/100000000000000 : ℝ)^3935
        have hw : |(1069248363/2000000000 : ℝ)|=(1069248363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-343986239/2000000000 : ℝ)|^4959 ≤ (2175700426901/20000000000000 : ℝ)^3935
        have hw : |(-343986239/2000000000 : ℝ)|=(343986239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5184478641/10000000000 : ℝ)|^4959 ≤ (5462270134757/12500000000000 : ℝ)^3935
        have hw : |(5184478641/10000000000 : ℝ)|=(5184478641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s3_2 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336560457/2500000000 : ℝ)*x 0 + (129611967/250000000 : ℝ)*x 1 + (-859965563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336560457/2500000000 : ℝ)^4959 ≤ (11355834229243/25000000000000 : ℝ)^3935 := by
    have hnat : (1336560457 : ℕ)^4959*25000000000000^3935 ≤ 11355834229243^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336560457 2500000000 11355834229243 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129611967/250000000 : ℝ)^4959 ≤ (8739632298463/20000000000000 : ℝ)^3935 := by
    have hnat : (129611967 : ℕ)^4959*20000000000000^3935 ≤ 8739632298463^3935*250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129611967 250000000 8739632298463 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (859965563/5000000000 : ℝ)^4959 ≤ (10878501584513/100000000000000 : ℝ)^3935 := by
    have hnat : (859965563 : ℕ)^4959*100000000000000^3935 ≤ 10878501584513^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859965563 5000000000 10878501584513 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336560457/2500000000 : ℝ), (129611967/250000000 : ℝ), (-859965563/5000000000 : ℝ)] ![(11355834229243/25000000000000 : ℝ), (8739632298463/20000000000000 : ℝ), (10878501584513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336560457/2500000000 : ℝ)|^4959 ≤ (11355834229243/25000000000000 : ℝ)^3935
        have hw : |(1336560457/2500000000 : ℝ)|=(1336560457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129611967/250000000 : ℝ)|^4959 ≤ (8739632298463/20000000000000 : ℝ)^3935
        have hw : |(129611967/250000000 : ℝ)|=(129611967/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-859965563/5000000000 : ℝ)|^4959 ≤ (10878501584513/100000000000000 : ℝ)^3935
        have hw : |(-859965563/5000000000 : ℝ)|=(859965563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s3_3 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (834624353/2000000000 : ℝ)*x 0 + (3842272221/10000000000 : ℝ)*x 1 + (452386471/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (834624353/2000000000 : ℝ)^4959 ≤ (8310633561581/25000000000000 : ℝ)^3935 := by
    have hnat : (834624353 : ℕ)^4959*25000000000000^3935 ≤ 8310633561581^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834624353 2000000000 8310633561581 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3842272221/10000000000 : ℝ)^4959 ≤ (3744519067211/12500000000000 : ℝ)^3935 := by
    have hnat : (3842272221 : ℕ)^4959*12500000000000^3935 ≤ 3744519067211^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3842272221 10000000000 3744519067211 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452386471/1000000000 : ℝ)^4959 ≤ (36801313193809/100000000000000 : ℝ)^3935 := by
    have hnat : (452386471 : ℕ)^4959*100000000000000^3935 ≤ 36801313193809^3935*1000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452386471 1000000000 36801313193809 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(834624353/2000000000 : ℝ), (3842272221/10000000000 : ℝ), (452386471/1000000000 : ℝ)] ![(8310633561581/25000000000000 : ℝ), (3744519067211/12500000000000 : ℝ), (36801313193809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(834624353/2000000000 : ℝ)|^4959 ≤ (8310633561581/25000000000000 : ℝ)^3935
        have hw : |(834624353/2000000000 : ℝ)|=(834624353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3842272221/10000000000 : ℝ)|^4959 ≤ (3744519067211/12500000000000 : ℝ)^3935
        have hw : |(3842272221/10000000000 : ℝ)|=(3842272221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452386471/1000000000 : ℝ)|^4959 ≤ (36801313193809/100000000000000 : ℝ)^3935
        have hw : |(452386471/1000000000 : ℝ)|=(452386471/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s3_4 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1586116233/10000000000 : ℝ)*x 0 + (5186456649/10000000000 : ℝ)*x 1 + (5442642541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1586116233/10000000000 : ℝ)^4959 ≤ (9822888531797/100000000000000 : ℝ)^3935 := by
    have hnat : (1586116233 : ℕ)^4959*100000000000000^3935 ≤ 9822888531797^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586116233 10000000000 9822888531797 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5186456649/10000000000 : ℝ)^4959 ≤ (2185958628869/5000000000000 : ℝ)^3935 := by
    have hnat : (5186456649 : ℕ)^4959*5000000000000^3935 ≤ 2185958628869^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5186456649 10000000000 2185958628869 5000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442642541/10000000000 : ℝ)^4959 ≤ (46457938879767/100000000000000 : ℝ)^3935 := by
    have hnat : (5442642541 : ℕ)^4959*100000000000000^3935 ≤ 46457938879767^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442642541 10000000000 46457938879767 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1586116233/10000000000 : ℝ), (5186456649/10000000000 : ℝ), (5442642541/10000000000 : ℝ)] ![(9822888531797/100000000000000 : ℝ), (2185958628869/5000000000000 : ℝ), (46457938879767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1586116233/10000000000 : ℝ)|^4959 ≤ (9822888531797/100000000000000 : ℝ)^3935
        have hw : |(-1586116233/10000000000 : ℝ)|=(1586116233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5186456649/10000000000 : ℝ)|^4959 ≤ (2185958628869/5000000000000 : ℝ)^3935
        have hw : |(5186456649/10000000000 : ℝ)|=(5186456649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442642541/10000000000 : ℝ)|^4959 ≤ (46457938879767/100000000000000 : ℝ)^3935
        have hw : |(5442642541/10000000000 : ℝ)|=(5442642541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s3_5 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276660531/10000000000 : ℝ)*x 0 + (-1461767231/10000000000 : ℝ)*x 1 + (2721321279/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276660531/10000000000 : ℝ)^4959 ≤ (44679575105609/100000000000000 : ℝ)^3935 := by
    have hnat : (5276660531 : ℕ)^4959*100000000000000^3935 ≤ 44679575105609^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276660531 10000000000 44679575105609 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1461767231/10000000000 : ℝ)^4959 ≤ (8862485820729/100000000000000 : ℝ)^3935 := by
    have hnat : (1461767231 : ℕ)^4959*100000000000000^3935 ≤ 8862485820729^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461767231 10000000000 8862485820729 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721321279/5000000000 : ℝ)^4959 ≤ (580724238283/1250000000000 : ℝ)^3935 := by
    have hnat : (2721321279 : ℕ)^4959*1250000000000^3935 ≤ 580724238283^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721321279 5000000000 580724238283 1250000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276660531/10000000000 : ℝ), (-1461767231/10000000000 : ℝ), (2721321279/5000000000 : ℝ)] ![(44679575105609/100000000000000 : ℝ), (8862485820729/100000000000000 : ℝ), (580724238283/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276660531/10000000000 : ℝ)|^4959 ≤ (44679575105609/100000000000000 : ℝ)^3935
        have hw : |(5276660531/10000000000 : ℝ)|=(5276660531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1461767231/10000000000 : ℝ)|^4959 ≤ (8862485820729/100000000000000 : ℝ)^3935
        have hw : |(-1461767231/10000000000 : ℝ)|=(1461767231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721321279/5000000000 : ℝ)|^4959 ≤ (580724238283/1250000000000 : ℝ)^3935
        have hw : |(2721321279/5000000000 : ℝ)|=(2721321279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s3_6 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055332111/2000000000 : ℝ)*x 0 + (5442642531/10000000000 : ℝ)*x 1 + (-730883617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055332111/2000000000 : ℝ)^4959 ≤ (44679575361709/100000000000000 : ℝ)^3935 := by
    have hnat : (1055332111 : ℕ)^4959*100000000000000^3935 ≤ 44679575361709^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055332111 2000000000 44679575361709 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442642531/10000000000 : ℝ)^4959 ≤ (9291587754439/20000000000000 : ℝ)^3935 := by
    have hnat : (5442642531 : ℕ)^4959*20000000000000^3935 ≤ 9291587754439^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442642531 10000000000 9291587754439 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (730883617/5000000000 : ℝ)^4959 ≤ (8862485843651/100000000000000 : ℝ)^3935 := by
    have hnat : (730883617 : ℕ)^4959*100000000000000^3935 ≤ 8862485843651^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730883617 5000000000 8862485843651 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055332111/2000000000 : ℝ), (5442642531/10000000000 : ℝ), (-730883617/5000000000 : ℝ)] ![(44679575361709/100000000000000 : ℝ), (9291587754439/20000000000000 : ℝ), (8862485843651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055332111/2000000000 : ℝ)|^4959 ≤ (44679575361709/100000000000000 : ℝ)^3935
        have hw : |(1055332111/2000000000 : ℝ)|=(1055332111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442642531/10000000000 : ℝ)|^4959 ≤ (9291587754439/20000000000000 : ℝ)^3935
        have hw : |(5442642531/10000000000 : ℝ)|=(5442642531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-730883617/5000000000 : ℝ)|^4959 ≤ (8862485843651/100000000000000 : ℝ)^3935
        have hw : |(-730883617/5000000000 : ℝ)|=(730883617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s3_7 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173287041/10000000000 : ℝ)*x 0 + (2259341431/5000000000 : ℝ)*x 1 + (1923754211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173287041/10000000000 : ℝ)^4959 ≤ (16622096715009/50000000000000 : ℝ)^3935 := by
    have hnat : (4173287041 : ℕ)^4959*50000000000000^3935 ≤ 16622096715009^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173287041 10000000000 16622096715009 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259341431/5000000000 : ℝ)^4959 ≤ (36748197482873/100000000000000 : ℝ)^3935 := by
    have hnat : (2259341431 : ℕ)^4959*100000000000000^3935 ≤ 36748197482873^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259341431 5000000000 36748197482873 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1923754211/5000000000 : ℝ)^4959 ≤ (1875475567197/6250000000000 : ℝ)^3935 := by
    have hnat : (1923754211 : ℕ)^4959*6250000000000^3935 ≤ 1875475567197^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923754211 5000000000 1875475567197 6250000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173287041/10000000000 : ℝ), (2259341431/5000000000 : ℝ), (1923754211/5000000000 : ℝ)] ![(16622096715009/50000000000000 : ℝ), (36748197482873/100000000000000 : ℝ), (1875475567197/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173287041/10000000000 : ℝ)|^4959 ≤ (16622096715009/50000000000000 : ℝ)^3935
        have hw : |(4173287041/10000000000 : ℝ)|=(4173287041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259341431/5000000000 : ℝ)|^4959 ≤ (36748197482873/100000000000000 : ℝ)^3935
        have hw : |(2259341431/5000000000 : ℝ)|=(2259341431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1923754211/5000000000 : ℝ)|^4959 ≤ (1875475567197/6250000000000 : ℝ)^3935
        have hw : |(1923754211/5000000000 : ℝ)|=(1923754211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1660_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5359/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4063/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16313/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5331/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16313/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5331/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16313/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5331/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5331/50000 : ℝ) ^ (4955/1024 : ℝ) ≤ (1976243611092831/100000000000000000000 : ℝ) := by
    have hpowers : (5331/50000 : ℝ)^4955 ≤ (1976243611092831/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5331 : ℕ)^4955*100000000000000000000^1024 ≤ 1976243611092831^1024*50000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5331 50000 1976243611092831 100000000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5331/50000 : ℝ)) (X := (1976243611092831/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16313/100000 : ℝ) ^ (4955/1024 : ℝ) ≤ (1934041690938329/12500000000000000000 : ℝ) := by
    have hpowers : (16313/100000 : ℝ)^4955 ≤ (1934041690938329/12500000000000000000 : ℝ)^1024 := by
      have hnat : (16313 : ℕ)^4955*12500000000000000000^1024 ≤ 1934041690938329^1024*100000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16313 100000 1934041690938329 12500000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16313/100000 : ℝ)) (X := (1934041690938329/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001976243611092831/50000000000000000000 : ℝ) ≤ (2000016336159279/2000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (50001976243611092831/50000000000000000000 : ℝ)^1024 ≤ (2000016336159279/2000000000000000 : ℝ)^4955 := by
      have hnat : (50001976243611092831 : ℕ)^1024*2000000000000000^4955 ≤ 2000016336159279^4955*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001976243611092831 50000000000000000000 2000016336159279 2000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000016336159279/2000000000000000 : ℝ)) (X := (50001976243611092831/50000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017448577138599463/100000000000000000000 : ℝ) ≤ (10000360567234341/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (100017448577138599463/100000000000000000000 : ℝ)^1024 ≤ (10000360567234341/10000000000000000 : ℝ)^4955 := by
      have hnat : (100017448577138599463 : ℕ)^1024*10000000000000000^4955 ≤ 10000360567234341^4955*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017448577138599463 100000000000000000000 10000360567234341 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000360567234341/10000000000000000 : ℝ)) (X := (100017448577138599463/100000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251934041690938329/6250000000000000000 : ℝ) ≤ (10000639453672287/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (6251934041690938329/6250000000000000000 : ℝ)^1024 ≤ (10000639453672287/10000000000000000 : ℝ)^4955 := by
      have hnat : (6251934041690938329 : ℕ)^1024*10000000000000000^4955 ≤ 10000639453672287^4955*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251934041690938329 6250000000000000000 10000639453672287 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000639453672287/10000000000000000 : ℝ)) (X := (6251934041690938329/6250000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1976243611092831/100000000000000000000 : ℝ) ≤ ((56504514603777667641/56510000000000000000 : ℝ)+2*(139443218973/282550000000000 : ℝ)*(5331/50000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (56504514603777667641/56510000000000000000 : ℝ)+2*(139443218973/282550000000000 : ℝ)*(5331/50000 : ℝ)=(2000016336159279/2000000000000000 : ℝ) by norm_num, show 1+2*(1976243611092831/100000000000000000000 : ℝ)=(50001976243611092831/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1934041690938329/12500000000000000000 : ℝ)+(1976243611092831/100000000000000000000 : ℝ) ≤ ((56504514603777667641/56510000000000000000 : ℝ)+(139443218973/282550000000000 : ℝ)*((16313/100000 : ℝ)+(5331/50000 : ℝ)))^(4955/1024 : ℝ) := by
    rw [show (56504514603777667641/56510000000000000000 : ℝ)+(139443218973/282550000000000 : ℝ)*((16313/100000 : ℝ)+(5331/50000 : ℝ))=(10000360567234341/10000000000000000 : ℝ) by norm_num, show 1+(1934041690938329/12500000000000000000 : ℝ)+(1976243611092831/100000000000000000000 : ℝ)=(100017448577138599463/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1934041690938329/12500000000000000000 : ℝ) ≤ ((56504514603777667641/56510000000000000000 : ℝ)+2*(139443218973/282550000000000 : ℝ)*(16313/100000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (56504514603777667641/56510000000000000000 : ℝ)+2*(139443218973/282550000000000 : ℝ)*(16313/100000 : ℝ)=(10000639453672287/10000000000000000 : ℝ) by norm_num, show 1+2*(1934041690938329/12500000000000000000 : ℝ)=(6251934041690938329/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (56504514603777667641/56510000000000000000 : ℝ)*(X 1 0+X 2 0)+(139443218973/282550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (56504514603777667641/56510000000000000000 : ℝ)) (alpha := (139443218973/282550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (56504514603777667641/56510000000000000000 : ℝ)*(X 0 1+X 2 1)+(139443218973/282550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (56504514603777667641/56510000000000000000 : ℝ)) (alpha := (139443218973/282550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (56504514603777667641/56510000000000000000 : ℝ)*(X 0 2+X 1 2)+(139443218973/282550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (5331/50000 : ℝ)) (hi := (16313/100000 : ℝ)) (c := (56504514603777667641/56510000000000000000 : ℝ)) (alpha := (139443218973/282550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-793026581/5000000000 : ℝ)*X 0 0+(5444641339/10000000000 : ℝ)*X 0 1+(5184478757/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069248363/2000000000 : ℝ)*X 1 0+(-343986239/2000000000 : ℝ)*X 1 1+(5184478641/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336560457/2500000000 : ℝ)*X 2 0+(129611967/250000000 : ℝ)*X 2 1+(-859965563/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((834624353/2000000000 : ℝ)*X 0 0+(3842272221/10000000000 : ℝ)*X 0 1+(452386471/1000000000 : ℝ)*X 0 2+(834624353/2000000000 : ℝ)*X 1 0+(3842272221/10000000000 : ℝ)*X 1 1+(452386471/1000000000 : ℝ)*X 1 2+(834624353/2000000000 : ℝ)*X 2 0+(3842272221/10000000000 : ℝ)*X 2 1+(452386471/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1586116233/10000000000 : ℝ)*X 0 0+(5186456649/10000000000 : ℝ)*X 0 1+(5442642541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276660531/10000000000 : ℝ)*X 1 0+(-1461767231/10000000000 : ℝ)*X 1 1+(2721321279/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055332111/2000000000 : ℝ)*X 2 0+(5442642531/10000000000 : ℝ)*X 2 1+(-730883617/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4173287041/10000000000 : ℝ)*X 0 0+(2259341431/5000000000 : ℝ)*X 0 1+(1923754211/5000000000 : ℝ)*X 0 2+(4173287041/10000000000 : ℝ)*X 1 0+(2259341431/5000000000 : ℝ)*X 1 1+(1923754211/5000000000 : ℝ)*X 1 2+(4173287041/10000000000 : ℝ)*X 2 0+(2259341431/5000000000 : ℝ)*X 2 1+(1923754211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9023710882216659460611/1765937500000000000000000000 : ℝ) := by norm_num
    linear_combination (307620657/50000000000000 : ℝ)*(base19) + (551835753/100000000000000 : ℝ)*(base23) + (19447519/50000000000000 : ℝ)*(lower2) + (31813957/50000000000000 : ℝ)*(upper3) + (68671983/100000000000000 : ℝ)*(upper5) + (331932568189623/12500000000000 : ℝ)*(major0) + (331932568189623/12500000000000 : ℝ)*(major1) + (331932568189623/12500000000000 : ℝ)*(major2) + (768751334332581/20000000000000 : ℝ)*(sp0) + (60058802199349/1562500000000 : ℝ)*(sp1) + (3843763404163897/100000000000000 : ℝ)*(sp2) + (9169715907379/625000000000 : ℝ)*(sp3) + (1456867349/20000000000000 : ℝ)*(sp4) + (2419524677/100000000000000 : ℝ)*(sp7) + (1467156964705317/100000000000000 : ℝ)*(f.failure) + (76875279119993/2000000000000 : ℝ)*(f.sum) + (1900937633723/14127500000000000000000000000 : ℝ)*base66 + (1459585779106860657/706375000000000000000000000000000 : ℝ)*base68 + (4986542932783110657/706375000000000000000000000000000 : ℝ)*base70 + (6219433881539014343/706375000000000000000000000000000 : ℝ)*base71 + (103818027054053/14127500000000000000000000000 : ℝ)*base74 + (953489296823639343/706375000000000000000000000000000 : ℝ)*base75 + (2139508036129514343/706375000000000000000000000000000 : ℝ)*base77 + (1548672847564360657/706375000000000000000000000000000 : ℝ)*base80 + (18210837548687/3531875000000000000000000000 : ℝ)*base82 + (51193491/10000000000000000000000 : ℝ)*base89 + (51193491/10000000000000000000000 : ℝ)*base91 + (51193491/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (296230963068746246101299/28255000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1498025221/100000000000000 : ℝ)*(base19) + (1679701521/100000000000000 : ℝ)*(base23) + (54938169/25000000000000 : ℝ)*(upper3) + (36583089/50000000000000 : ℝ)*(lower4) + (208910509/100000000000000 : ℝ)*(upper5) + (2696670020017157/100000000000000 : ℝ)*(major0) + (2696670020017157/100000000000000 : ℝ)*(major1) + (2696670020017157/100000000000000 : ℝ)*(major2) + (3637896199/20000000000000 : ℝ)*(sp1) + (10052618043/50000000000000 : ℝ)*(sp2) + (195170712910321/5000000000000 : ℝ)*(sp4) + (975848642675051/25000000000000 : ℝ)*(sp5) + (1951696236634407/50000000000000 : ℝ)*(sp6) + (372481358088671/25000000000000 : ℝ)*(sp7) + (372481358088671/25000000000000 : ℝ)*(f.failure) + (195170712910321/5000000000000 : ℝ)*(f.sum) + (38847530014699/14127500000000000000000000000 : ℝ)*base66 + (10143904645827916637/5651000000000000000000000000000000 : ℝ)*base67 + (49003290504147916637/5651000000000000000000000000000000 : ℝ)*base69 + (18116380060472916637/5651000000000000000000000000000000 : ℝ)*base71 + (2045147765477/28255000000000000000000000000 : ℝ)*base73 + (6101285491809083363/5651000000000000000000000000000000 : ℝ)*base76 + (1302618741106083363/5651000000000000000000000000000000 : ℝ)*base78 + (1624235799406083363/5651000000000000000000000000000000 : ℝ)*base80 + (13621141060421/14127500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (5454967/2500000000000000000000 : ℝ)*base90 + (5454967/2500000000000000000000 : ℝ)*base92 + (5454967/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1660_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5359/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1660_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1660_s4_0 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-198260953/1250000000 : ℝ)*x 0 + (5444461329/10000000000 : ℝ)*x 1 + (648079469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (198260953/1250000000 : ℝ)^4959 ≤ (4911332624507/50000000000000 : ℝ)^3935 := by
    have hnat : (198260953 : ℕ)^4959*50000000000000^3935 ≤ 4911332624507^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198260953 1250000000 4911332624507 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444461329/10000000000 : ℝ)^4959 ≤ (9295500961631/20000000000000 : ℝ)^3935 := by
    have hnat : (5444461329 : ℕ)^4959*20000000000000^3935 ≤ 9295500961631^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444461329 10000000000 9295500961631 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648079469/1250000000 : ℝ)^4959 ≤ (43699829922083/100000000000000 : ℝ)^3935 := by
    have hnat : (648079469 : ℕ)^4959*100000000000000^3935 ≤ 43699829922083^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648079469 1250000000 43699829922083 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-198260953/1250000000 : ℝ), (5444461329/10000000000 : ℝ), (648079469/1250000000 : ℝ)] ![(4911332624507/50000000000000 : ℝ), (9295500961631/20000000000000 : ℝ), (43699829922083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-198260953/1250000000 : ℝ)|^4959 ≤ (4911332624507/50000000000000 : ℝ)^3935
        have hw : |(-198260953/1250000000 : ℝ)|=(198260953/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444461329/10000000000 : ℝ)|^4959 ≤ (9295500961631/20000000000000 : ℝ)^3935
        have hw : |(5444461329/10000000000 : ℝ)|=(5444461329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648079469/1250000000 : ℝ)|^4959 ≤ (43699829922083/100000000000000 : ℝ)^3935
        have hw : |(648079469/1250000000 : ℝ)|=(648079469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s4_1 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346193223/10000000000 : ℝ)*x 0 + (-859893549/5000000000 : ℝ)*x 1 + (648079469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346193223/10000000000 : ℝ)^4959 ≤ (45422816489467/100000000000000 : ℝ)^3935 := by
    have hnat : (5346193223 : ℕ)^4959*100000000000000^3935 ≤ 45422816489467^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346193223 10000000000 45422816489467 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (859893549/5000000000 : ℝ)^4959 ≤ (5438676782073/50000000000000 : ℝ)^3935 := by
    have hnat : (859893549 : ℕ)^4959*50000000000000^3935 ≤ 5438676782073^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859893549 5000000000 5438676782073 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (648079469/1250000000 : ℝ)^4959 ≤ (43699829922083/100000000000000 : ℝ)^3935 := by
    have hnat : (648079469 : ℕ)^4959*100000000000000^3935 ≤ 43699829922083^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648079469 1250000000 43699829922083 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346193223/10000000000 : ℝ), (-859893549/5000000000 : ℝ), (648079469/1250000000 : ℝ)] ![(45422816489467/100000000000000 : ℝ), (5438676782073/50000000000000 : ℝ), (43699829922083/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346193223/10000000000 : ℝ)|^4959 ≤ (45422816489467/100000000000000 : ℝ)^3935
        have hw : |(5346193223/10000000000 : ℝ)|=(5346193223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-859893549/5000000000 : ℝ)|^4959 ≤ (5438676782073/50000000000000 : ℝ)^3935
        have hw : |(-859893549/5000000000 : ℝ)|=(859893549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(648079469/1250000000 : ℝ)|^4959 ≤ (43699829922083/100000000000000 : ℝ)^3935
        have hw : |(648079469/1250000000 : ℝ)|=(648079469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s4_2 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346193223/10000000000 : ℝ)*x 0 + (1036927151/2000000000 : ℝ)*x 1 + (-343957419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346193223/10000000000 : ℝ)^4959 ≤ (45422816489467/100000000000000 : ℝ)^3935 := by
    have hnat : (5346193223 : ℕ)^4959*100000000000000^3935 ≤ 45422816489467^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346193223 10000000000 45422816489467 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036927151/2000000000 : ℝ)^4959 ≤ (43699829953949/100000000000000 : ℝ)^3935 := by
    have hnat : (1036927151 : ℕ)^4959*100000000000000^3935 ≤ 43699829953949^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036927151 2000000000 43699829953949 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343957419/2000000000 : ℝ)^4959 ≤ (5438676770117/50000000000000 : ℝ)^3935 := by
    have hnat : (343957419 : ℕ)^4959*50000000000000^3935 ≤ 5438676770117^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343957419 2000000000 5438676770117 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346193223/10000000000 : ℝ), (1036927151/2000000000 : ℝ), (-343957419/2000000000 : ℝ)] ![(45422816489467/100000000000000 : ℝ), (43699829953949/100000000000000 : ℝ), (5438676770117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346193223/10000000000 : ℝ)|^4959 ≤ (45422816489467/100000000000000 : ℝ)^3935
        have hw : |(5346193223/10000000000 : ℝ)|=(5346193223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036927151/2000000000 : ℝ)|^4959 ≤ (43699829953949/100000000000000 : ℝ)^3935
        have hw : |(1036927151/2000000000 : ℝ)|=(1036927151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343957419/2000000000 : ℝ)|^4959 ≤ (5438676770117/50000000000000 : ℝ)^3935
        have hw : |(-343957419/2000000000 : ℝ)|=(343957419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s4_3 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2086572697/5000000000 : ℝ)*x 0 + (768542217/2000000000 : ℝ)*x 1 + (1130855239/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2086572697/5000000000 : ℝ)^4959 ≤ (8310692863413/25000000000000 : ℝ)^3935 := by
    have hnat : (2086572697 : ℕ)^4959*25000000000000^3935 ≤ 8310692863413^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086572697 5000000000 8310692863413 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (768542217/2000000000 : ℝ)^4959 ≤ (7490116146667/25000000000000 : ℝ)^3935 := by
    have hnat : (768542217 : ℕ)^4959*25000000000000^3935 ≤ 7490116146667^3935*2000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768542217 2000000000 7490116146667 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130855239/2500000000 : ℝ)^4959 ≤ (4599595492959/12500000000000 : ℝ)^3935 := by
    have hnat : (1130855239 : ℕ)^4959*12500000000000^3935 ≤ 4599595492959^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130855239 2500000000 4599595492959 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2086572697/5000000000 : ℝ), (768542217/2000000000 : ℝ), (1130855239/2500000000 : ℝ)] ![(8310692863413/25000000000000 : ℝ), (7490116146667/25000000000000 : ℝ), (4599595492959/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2086572697/5000000000 : ℝ)|^4959 ≤ (8310692863413/25000000000000 : ℝ)^3935
        have hw : |(2086572697/5000000000 : ℝ)|=(2086572697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(768542217/2000000000 : ℝ)|^4959 ≤ (7490116146667/25000000000000 : ℝ)^3935
        have hw : |(768542217/2000000000 : ℝ)|=(768542217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1130855239/2500000000 : ℝ)|^4959 ≤ (4599595492959/12500000000000 : ℝ)^3935
        have hw : |(1130855239/2500000000 : ℝ)|=(1130855239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s4_4 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-158615033/1000000000 : ℝ)*x 0 + (2593304283/5000000000 : ℝ)*x 1 + (2721233889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (158615033/1000000000 : ℝ)^4959 ≤ (9823154647781/100000000000000 : ℝ)^3935 := by
    have hnat : (158615033 : ℕ)^4959*100000000000000^3935 ≤ 9823154647781^3935*1000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158615033 1000000000 9823154647781 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2593304283/5000000000 : ℝ)^4959 ≤ (43720786410351/100000000000000 : ℝ)^3935 := by
    have hnat : (2593304283 : ℕ)^4959*100000000000000^3935 ≤ 43720786410351^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2593304283 5000000000 43720786410351 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721233889/5000000000 : ℝ)^4959 ≤ (1858242357039/4000000000000 : ℝ)^3935 := by
    have hnat : (2721233889 : ℕ)^4959*4000000000000^3935 ≤ 1858242357039^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721233889 5000000000 1858242357039 4000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-158615033/1000000000 : ℝ), (2593304283/5000000000 : ℝ), (2721233889/5000000000 : ℝ)] ![(9823154647781/100000000000000 : ℝ), (43720786410351/100000000000000 : ℝ), (1858242357039/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-158615033/1000000000 : ℝ)|^4959 ≤ (9823154647781/100000000000000 : ℝ)^3935
        have hw : |(-158615033/1000000000 : ℝ)|=(158615033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2593304283/5000000000 : ℝ)|^4959 ≤ (43720786410351/100000000000000 : ℝ)^3935
        have hw : |(2593304283/5000000000 : ℝ)|=(2593304283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721233889/5000000000 : ℝ)|^4959 ≤ (1858242357039/4000000000000 : ℝ)^3935
        have hw : |(2721233889/5000000000 : ℝ)|=(2721233889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s4_5 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276702161/10000000000 : ℝ)*x 0 + (-730977567/5000000000 : ℝ)*x 1 + (1360616949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276702161/10000000000 : ℝ)^4959 ≤ (44680019333791/100000000000000 : ℝ)^3935 := by
    have hnat : (5276702161 : ℕ)^4959*100000000000000^3935 ≤ 44680019333791^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276702161 10000000000 44680019333791 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (730977567/5000000000 : ℝ)^4959 ≤ (8863921533887/100000000000000 : ℝ)^3935 := by
    have hnat : (730977567 : ℕ)^4959*100000000000000^3935 ≤ 8863921533887^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      730977567 5000000000 8863921533887 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360616949/2500000000 : ℝ)^4959 ≤ (46456059119603/100000000000000 : ℝ)^3935 := by
    have hnat : (1360616949 : ℕ)^4959*100000000000000^3935 ≤ 46456059119603^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360616949 2500000000 46456059119603 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276702161/10000000000 : ℝ), (-730977567/5000000000 : ℝ), (1360616949/2500000000 : ℝ)] ![(44680019333791/100000000000000 : ℝ), (8863921533887/100000000000000 : ℝ), (46456059119603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276702161/10000000000 : ℝ)|^4959 ≤ (44680019333791/100000000000000 : ℝ)^3935
        have hw : |(5276702161/10000000000 : ℝ)|=(5276702161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-730977567/5000000000 : ℝ)|^4959 ≤ (8863921533887/100000000000000 : ℝ)^3935
        have hw : |(-730977567/5000000000 : ℝ)|=(730977567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360616949/2500000000 : ℝ)|^4959 ≤ (46456059119603/100000000000000 : ℝ)^3935
        have hw : |(1360616949/2500000000 : ℝ)|=(1360616949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s4_6 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276702153/10000000000 : ℝ)*x 0 + (217698713/400000000 : ℝ)*x 1 + (-45686097/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276702153/10000000000 : ℝ)^4959 ≤ (5585002406053/12500000000000 : ℝ)^3935 := by
    have hnat : (5276702153 : ℕ)^4959*12500000000000^3935 ≤ 5585002406053^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276702153 10000000000 5585002406053 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217698713/400000000 : ℝ)^4959 ≤ (1161401485789/2500000000000 : ℝ)^3935 := by
    have hnat : (217698713 : ℕ)^4959*2500000000000^3935 ≤ 1161401485789^3935*400000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217698713 400000000 1161401485789 2500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (45686097/312500000 : ℝ)^4959 ≤ (8863921304661/100000000000000 : ℝ)^3935 := by
    have hnat : (45686097 : ℕ)^4959*100000000000000^3935 ≤ 8863921304661^3935*312500000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45686097 312500000 8863921304661 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276702153/10000000000 : ℝ), (217698713/400000000 : ℝ), (-45686097/312500000 : ℝ)] ![(5585002406053/12500000000000 : ℝ), (1161401485789/2500000000000 : ℝ), (8863921304661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276702153/10000000000 : ℝ)|^4959 ≤ (5585002406053/12500000000000 : ℝ)^3935
        have hw : |(5276702153/10000000000 : ℝ)|=(5276702153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217698713/400000000 : ℝ)|^4959 ≤ (1161401485789/2500000000000 : ℝ)^3935
        have hw : |(217698713/400000000 : ℝ)|=(217698713/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-45686097/312500000 : ℝ)|^4959 ≤ (8863921304661/100000000000000 : ℝ)^3935
        have hw : |(-45686097/312500000 : ℝ)|=(45686097/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_s4_7 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (130415933/312500000 : ℝ)*x 0 + (11295631/25000000 : ℝ)*x 1 + (961983491/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130415933/312500000 : ℝ)^4959 ≤ (33244422468099/100000000000000 : ℝ)^3935 := by
    have hnat : (130415933 : ℕ)^4959*100000000000000^3935 ≤ 33244422468099^3935*312500000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130415933 312500000 33244422468099 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11295631/25000000 : ℝ)^4959 ≤ (36743785813197/100000000000000 : ℝ)^3935 := by
    have hnat : (11295631 : ℕ)^4959*100000000000000^3935 ≤ 36743785813197^3935*25000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11295631 25000000 36743785813197 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961983491/2500000000 : ℝ)^4959 ≤ (3751473963647/12500000000000 : ℝ)^3935 := by
    have hnat : (961983491 : ℕ)^4959*12500000000000^3935 ≤ 3751473963647^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961983491 2500000000 3751473963647 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(130415933/312500000 : ℝ), (11295631/25000000 : ℝ), (961983491/2500000000 : ℝ)] ![(33244422468099/100000000000000 : ℝ), (36743785813197/100000000000000 : ℝ), (3751473963647/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(130415933/312500000 : ℝ)|^4959 ≤ (33244422468099/100000000000000 : ℝ)^3935
        have hw : |(130415933/312500000 : ℝ)|=(130415933/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11295631/25000000 : ℝ)|^4959 ≤ (36743785813197/100000000000000 : ℝ)^3935
        have hw : |(11295631/25000000 : ℝ)|=(11295631/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961983491/2500000000 : ℝ)|^4959 ≤ (3751473963647/12500000000000 : ℝ)^3935
        have hw : |(961983491/2500000000 : ℝ)|=(961983491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1660_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5359/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10721/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2031/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4063/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5359/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4063/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5359/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4063/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5359/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4063/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5359/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4063/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5359/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4063/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5359/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5359/50000 : ℝ) ^ (4955/1024 : ℝ) ≤ (2026979060909947/100000000000000000000 : ℝ) := by
    have hpowers : (5359/50000 : ℝ)^4955 ≤ (2026979060909947/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5359 : ℕ)^4955*100000000000000000000^1024 ≤ 2026979060909947^1024*50000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5359 50000 2026979060909947 100000000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5359/50000 : ℝ)) (X := (2026979060909947/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4063/25000 : ℝ) ^ (4955/1024 : ℝ) ≤ (15194376121075529/100000000000000000000 : ℝ) := by
    have hpowers : (4063/25000 : ℝ)^4955 ≤ (15194376121075529/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4063 : ℕ)^4955*100000000000000000000^1024 ≤ 15194376121075529^1024*25000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4063 25000 15194376121075529 100000000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4063/25000 : ℝ)) (X := (15194376121075529/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002026979060909947/50000000000000000000 : ℝ) ≤ (2500020944431699/2500000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (50002026979060909947/50000000000000000000 : ℝ)^1024 ≤ (2500020944431699/2500000000000000 : ℝ)^4955 := by
      have hnat : (50002026979060909947 : ℕ)^1024*2500000000000000^4955 ≤ 2500020944431699^4955*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002026979060909947 50000000000000000000 2500020944431699 2500000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500020944431699/2500000000000000 : ℝ)) (X := (50002026979060909947/50000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25004305338795496369/25000000000000000000 : ℝ) ≤ (10000355872112447/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (25004305338795496369/25000000000000000000 : ℝ)^1024 ≤ (10000355872112447/10000000000000000 : ℝ)^4955 := by
      have hnat : (25004305338795496369 : ℕ)^1024*10000000000000000^4955 ≤ 10000355872112447^4955*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004305338795496369 25000000000000000000 10000355872112447 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000355872112447/10000000000000000 : ℝ)) (X := (25004305338795496369/25000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50015194376121075529/50000000000000000000 : ℝ) ≤ (5000313983249049/5000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (50015194376121075529/50000000000000000000 : ℝ)^1024 ≤ (5000313983249049/5000000000000000 : ℝ)^4955 := by
      have hnat : (50015194376121075529 : ℕ)^1024*5000000000000000^4955 ≤ 5000313983249049^4955*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50015194376121075529 50000000000000000000 5000313983249049 5000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000313983249049/5000000000000000 : ℝ)) (X := (50015194376121075529/50000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2026979060909947/100000000000000000000 : ℝ) ≤ ((13833657752672318557/13835000000000000000 : ℝ)+2*(272094385651/553400000000000 : ℝ)*(5359/50000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (13833657752672318557/13835000000000000000 : ℝ)+2*(272094385651/553400000000000 : ℝ)*(5359/50000 : ℝ)=(2500020944431699/2500000000000000 : ℝ) by norm_num, show 1+2*(2026979060909947/100000000000000000000 : ℝ)=(50002026979060909947/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15194376121075529/100000000000000000000 : ℝ)+(2026979060909947/100000000000000000000 : ℝ) ≤ ((13833657752672318557/13835000000000000000 : ℝ)+(272094385651/553400000000000 : ℝ)*((4063/25000 : ℝ)+(5359/50000 : ℝ)))^(4955/1024 : ℝ) := by
    rw [show (13833657752672318557/13835000000000000000 : ℝ)+(272094385651/553400000000000 : ℝ)*((4063/25000 : ℝ)+(5359/50000 : ℝ))=(10000355872112447/10000000000000000 : ℝ) by norm_num, show 1+(15194376121075529/100000000000000000000 : ℝ)+(2026979060909947/100000000000000000000 : ℝ)=(25004305338795496369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15194376121075529/100000000000000000000 : ℝ) ≤ ((13833657752672318557/13835000000000000000 : ℝ)+2*(272094385651/553400000000000 : ℝ)*(4063/25000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (13833657752672318557/13835000000000000000 : ℝ)+2*(272094385651/553400000000000 : ℝ)*(4063/25000 : ℝ)=(5000313983249049/5000000000000000 : ℝ) by norm_num, show 1+2*(15194376121075529/100000000000000000000 : ℝ)=(50015194376121075529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13833657752672318557/13835000000000000000 : ℝ)*(X 1 0+X 2 0)+(272094385651/553400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (5359/50000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (13833657752672318557/13835000000000000000 : ℝ)) (alpha := (272094385651/553400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13833657752672318557/13835000000000000000 : ℝ)*(X 0 1+X 2 1)+(272094385651/553400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (5359/50000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (13833657752672318557/13835000000000000000 : ℝ)) (alpha := (272094385651/553400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13833657752672318557/13835000000000000000 : ℝ)*(X 0 2+X 1 2)+(272094385651/553400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (5359/50000 : ℝ)) (hi := (4063/25000 : ℝ)) (c := (13833657752672318557/13835000000000000000 : ℝ)) (alpha := (272094385651/553400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-198260953/1250000000 : ℝ)*X 0 0+(5444461329/10000000000 : ℝ)*X 0 1+(648079469/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346193223/10000000000 : ℝ)*X 1 0+(-859893549/5000000000 : ℝ)*X 1 1+(648079469/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346193223/10000000000 : ℝ)*X 2 0+(1036927151/2000000000 : ℝ)*X 2 1+(-343957419/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2086572697/5000000000 : ℝ)*X 0 0+(768542217/2000000000 : ℝ)*X 0 1+(1130855239/2500000000 : ℝ)*X 0 2+(2086572697/5000000000 : ℝ)*X 1 0+(768542217/2000000000 : ℝ)*X 1 1+(1130855239/2500000000 : ℝ)*X 1 2+(2086572697/5000000000 : ℝ)*X 2 0+(768542217/2000000000 : ℝ)*X 2 1+(1130855239/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-158615033/1000000000 : ℝ)*X 0 0+(2593304283/5000000000 : ℝ)*X 0 1+(2721233889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276702161/10000000000 : ℝ)*X 1 0+(-730977567/5000000000 : ℝ)*X 1 1+(1360616949/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276702153/10000000000 : ℝ)*X 2 0+(217698713/400000000 : ℝ)*X 2 1+(-45686097/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((130415933/312500000 : ℝ)*X 0 0+(11295631/25000000 : ℝ)*X 0 1+(961983491/2500000000 : ℝ)*X 0 2+(130415933/312500000 : ℝ)*X 1 0+(11295631/25000000 : ℝ)*X 1 1+(961983491/2500000000 : ℝ)*X 1 2+(130415933/312500000 : ℝ)*X 2 0+(11295631/25000000 : ℝ)*X 2 1+(961983491/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6174902141711424565255376487/691750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (87634181/6250000000000 : ℝ)*(base19) + (1312045161/100000000000000 : ℝ)*(base23) + (3010633/6250000000000 : ℝ)*(lower2) + (54271859/25000000000000 : ℝ)*(upper3) + (9731253/6250000000000 : ℝ)*(upper5) + (2658920297849499/100000000000000 : ℝ)*(major0) + (2658920297849499/100000000000000 : ℝ)*(major1) + (2658920297849499/100000000000000 : ℝ)*(major2) + (1924377016720057/50000000000000 : ℝ)*(sp0) + (481096299821587/12500000000000 : ℝ)*(sp1) + (384877048867443/10000000000000 : ℝ)*(sp2) + (734530585638383/50000000000000 : ℝ)*(sp3) + (17767279477/100000000000000 : ℝ)*(sp4) + (1831538209/25000000000000 : ℝ)*(sp7) + (734534248714801/50000000000000 : ℝ)*(f.failure) + (481096475089949/12500000000000 : ℝ)*(f.sum) + (23270390844731/27670000000000000000000000000 : ℝ)*base66 + (5011576886890922057/1383500000000000000000000000000000 : ℝ)*base68 + (315796698196922057/1383500000000000000000000000000000 : ℝ)*base70 + (8371541707995922057/1383500000000000000000000000000000 : ℝ)*base72 + (39101516487491/27670000000000000000000000000 : ℝ)*base74 + (20465200766689922057/1383500000000000000000000000000000 : ℝ)*base76 + (7944522609542922057/1383500000000000000000000000000000 : ℝ)*base78 + (3486535376517922057/1383500000000000000000000000000000 : ℝ)*base80 + (38649300624349/27670000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (23285977/5000000000000000000000 : ℝ)*base90 + (23285977/5000000000000000000000 : ℝ)*base92 + (23285977/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13900215165227051322663/1729375000000000000000000000 : ℝ) := by norm_num
    linear_combination (1036230267/100000000000000 : ℝ)*(base19) + (148646953/12500000000000 : ℝ)*(base23) + (39656149/12500000000000 : ℝ)*(lower1) + (8102559/5000000000000 : ℝ)*(upper3) + (70372969/100000000000000 : ℝ)*(lower4) + (171260483/100000000000000 : ℝ)*(upper5) + (337513101467217/12500000000000 : ℝ)*(major0) + (337513101467217/12500000000000 : ℝ)*(major1) + (337513101467217/12500000000000 : ℝ)*(major2) + (242089679/12500000000000 : ℝ)*(sp2) + (156335447254081/4000000000000 : ℝ)*(sp4) + (1954192572560879/50000000000000 : ℝ)*(sp5) + (3908383055458969/100000000000000 : ℝ)*(sp6) + (745911587099877/50000000000000 : ℝ)*(sp7) + (745911587099877/50000000000000 : ℝ)*(f.failure) + (156335447254081/4000000000000 : ℝ)*(f.sum) + (6708700405389/6917500000000000000000000000 : ℝ)*base65 + (7203418737982295869/172937500000000000000000000000000 : ℝ)*base67 + (145878452733454131/172937500000000000000000000000000 : ℝ)*base70 + (14097928649475795869/172937500000000000000000000000000 : ℝ)*base71 + (4281640426789/1729375000000000000000000000 : ℝ)*base74 + (7733745581365079131/172937500000000000000000000000000 : ℝ)*base76 + (106748005495483369/172937500000000000000000000000000 : ℝ)*base77 + (119223229058016631/172937500000000000000000000000000 : ℝ)*base80 + (20679534633833/3458750000000000000000000000 : ℝ)*base82 + (1084371/5000000000000000000000 : ℝ)*base89 + (1084371/5000000000000000000000 : ℝ)*base91 + (1084371/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1660_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4063/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5359/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2031/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1660_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1660_box_0 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-665819743/5000000000 : ℝ)*x 0 + (675701963/1250000000 : ℝ)*x 1 + (1351404243/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (665819743/5000000000 : ℝ)^4959 ≤ (3940006462773/50000000000000 : ℝ)^3935 := by
    have hnat : (665819743 : ℕ)^4959*50000000000000^3935 ≤ 3940006462773^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      665819743 5000000000 3940006462773 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675701963/1250000000 : ℝ)^4959 ≤ (23029993360293/50000000000000 : ℝ)^3935 := by
    have hnat : (675701963 : ℕ)^4959*50000000000000^3935 ≤ 23029993360293^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675701963 1250000000 23029993360293 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351404243/2500000000 : ℝ)^4959 ≤ (9212000067303/20000000000000 : ℝ)^3935 := by
    have hnat : (1351404243 : ℕ)^4959*20000000000000^3935 ≤ 9212000067303^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351404243 2500000000 9212000067303 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-665819743/5000000000 : ℝ), (675701963/1250000000 : ℝ), (1351404243/2500000000 : ℝ)] ![(3940006462773/50000000000000 : ℝ), (23029993360293/50000000000000 : ℝ), (9212000067303/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-665819743/5000000000 : ℝ)|^4959 ≤ (3940006462773/50000000000000 : ℝ)^3935
        have hw : |(-665819743/5000000000 : ℝ)|=(665819743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675701963/1250000000 : ℝ)|^4959 ≤ (23029993360293/50000000000000 : ℝ)^3935
        have hw : |(675701963/1250000000 : ℝ)|=(675701963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351404243/2500000000 : ℝ)|^4959 ≤ (9212000067303/20000000000000 : ℝ)^3935
        have hw : |(1351404243/2500000000 : ℝ)|=(1351404243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_1 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328181969/625000000 : ℝ)*x 0 + (-1549119447/10000000000 : ℝ)*x 1 + (2702808073/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328181969/625000000 : ℝ)^4959 ≤ (22202492809237/50000000000000 : ℝ)^3935 := by
    have hnat : (328181969 : ℕ)^4959*50000000000000^3935 ≤ 22202492809237^3935*625000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328181969 625000000 22202492809237 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1549119447/10000000000 : ℝ)^4959 ≤ (4767511449881/50000000000000 : ℝ)^3935 := by
    have hnat : (1549119447 : ℕ)^4959*50000000000000^3935 ≤ 4767511449881^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1549119447 10000000000 4767511449881 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702808073/5000000000 : ℝ)^4959 ≤ (2878749466677/6250000000000 : ℝ)^3935 := by
    have hnat : (2702808073 : ℕ)^4959*6250000000000^3935 ≤ 2878749466677^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702808073 5000000000 2878749466677 6250000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328181969/625000000 : ℝ), (-1549119447/10000000000 : ℝ), (2702808073/5000000000 : ℝ)] ![(22202492809237/50000000000000 : ℝ), (4767511449881/50000000000000 : ℝ), (2878749466677/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328181969/625000000 : ℝ)|^4959 ≤ (22202492809237/50000000000000 : ℝ)^3935
        have hw : |(328181969/625000000 : ℝ)|=(328181969/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1549119447/10000000000 : ℝ)|^4959 ≤ (4767511449881/50000000000000 : ℝ)^3935
        have hw : |(-1549119447/10000000000 : ℝ)|=(1549119447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702808073/5000000000 : ℝ)|^4959 ≤ (2878749466677/6250000000000 : ℝ)^3935
        have hw : |(2702808073/5000000000 : ℝ)|=(2702808073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_2 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164090979/312500000 : ℝ)*x 0 + (5405616659/10000000000 : ℝ)*x 1 + (-774559489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164090979/312500000 : ℝ)^4959 ≤ (44404983742793/100000000000000 : ℝ)^3935 := by
    have hnat : (164090979 : ℕ)^4959*100000000000000^3935 ≤ 44404983742793^3935*312500000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164090979 312500000 44404983742793 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405616659/10000000000 : ℝ)^4959 ≤ (9211999395097/20000000000000 : ℝ)^3935 := by
    have hnat : (5405616659 : ℕ)^4959*20000000000000^3935 ≤ 9211999395097^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405616659 10000000000 9211999395097 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (774559489/5000000000 : ℝ)^4959 ≤ (9535019261793/100000000000000 : ℝ)^3935 := by
    have hnat : (774559489 : ℕ)^4959*100000000000000^3935 ≤ 9535019261793^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774559489 5000000000 9535019261793 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164090979/312500000 : ℝ), (5405616659/10000000000 : ℝ), (-774559489/5000000000 : ℝ)] ![(44404983742793/100000000000000 : ℝ), (9211999395097/20000000000000 : ℝ), (9535019261793/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164090979/312500000 : ℝ)|^4959 ≤ (44404983742793/100000000000000 : ℝ)^3935
        have hw : |(164090979/312500000 : ℝ)|=(164090979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405616659/10000000000 : ℝ)|^4959 ≤ (9211999395097/20000000000000 : ℝ)^3935
        have hw : |(5405616659/10000000000 : ℝ)|=(5405616659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-774559489/5000000000 : ℝ)|^4959 ≤ (9535019261793/100000000000000 : ℝ)^3935
        have hw : |(-774559489/5000000000 : ℝ)|=(774559489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_3 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4449303849/10000000000 : ℝ)*x 0 + (1011731801/2500000000 : ℝ)*x 1 + (4046927581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4449303849/10000000000 : ℝ)^4959 ≤ (36038570902427/100000000000000 : ℝ)^3935 := by
    have hnat : (4449303849 : ℕ)^4959*100000000000000^3935 ≤ 36038570902427^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4449303849 10000000000 36038570902427 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1011731801/2500000000 : ℝ)^4959 ≤ (31980712666159/100000000000000 : ℝ)^3935 := by
    have hnat : (1011731801 : ℕ)^4959*100000000000000^3935 ≤ 31980712666159^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1011731801 2500000000 31980712666159 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4046927581/10000000000 : ℝ)^4959 ≤ (31980716420671/100000000000000 : ℝ)^3935 := by
    have hnat : (4046927581 : ℕ)^4959*100000000000000^3935 ≤ 31980716420671^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4046927581 10000000000 31980716420671 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4449303849/10000000000 : ℝ), (1011731801/2500000000 : ℝ), (4046927581/10000000000 : ℝ)] ![(36038570902427/100000000000000 : ℝ), (31980712666159/100000000000000 : ℝ), (31980716420671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4449303849/10000000000 : ℝ)|^4959 ≤ (36038570902427/100000000000000 : ℝ)^3935
        have hw : |(4449303849/10000000000 : ℝ)|=(4449303849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1011731801/2500000000 : ℝ)|^4959 ≤ (31980712666159/100000000000000 : ℝ)^3935
        have hw : |(1011731801/2500000000 : ℝ)|=(1011731801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4046927581/10000000000 : ℝ)|^4959 ≤ (31980716420671/100000000000000 : ℝ)^3935
        have hw : |(4046927581/10000000000 : ℝ)|=(4046927581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_4 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-5784691/31250000 : ℝ)*x 0 + (2607983117/5000000000 : ℝ)*x 1 + (5215965773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5784691/31250000 : ℝ)^4959 ≤ (5967115364833/50000000000000 : ℝ)^3935 := by
    have hnat : (5784691 : ℕ)^4959*50000000000000^3935 ≤ 5967115364833^3935*31250000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5784691 31250000 5967115364833 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607983117/5000000000 : ℝ)^4959 ≤ (44032887084447/100000000000000 : ℝ)^3935 := by
    have hnat : (2607983117 : ℕ)^4959*100000000000000^3935 ≤ 44032887084447^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607983117 5000000000 44032887084447 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215965773/10000000000 : ℝ)^4959 ≤ (4403288217997/10000000000000 : ℝ)^3935 := by
    have hnat : (5215965773 : ℕ)^4959*10000000000000^3935 ≤ 4403288217997^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215965773 10000000000 4403288217997 10000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5784691/31250000 : ℝ), (2607983117/5000000000 : ℝ), (5215965773/10000000000 : ℝ)] ![(5967115364833/50000000000000 : ℝ), (44032887084447/100000000000000 : ℝ), (4403288217997/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5784691/31250000 : ℝ)|^4959 ≤ (5967115364833/50000000000000 : ℝ)^3935
        have hw : |(-5784691/31250000 : ℝ)|=(5784691/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607983117/5000000000 : ℝ)|^4959 ≤ (44032887084447/100000000000000 : ℝ)^3935
        have hw : |(2607983117/5000000000 : ℝ)|=(2607983117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215965773/10000000000 : ℝ)|^4959 ≤ (4403288217997/10000000000000 : ℝ)^3935
        have hw : |(5215965773/10000000000 : ℝ)|=(5215965773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_5 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10509589/19531250 : ℝ)*x 0 + (-203839929/1250000000 : ℝ)*x 1 + (521596619/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10509589/19531250 : ℝ)^4959 ≤ (915896947203/2000000000000 : ℝ)^3935 := by
    have hnat : (10509589 : ℕ)^4959*2000000000000^3935 ≤ 915896947203^3935*19531250^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10509589 19531250 915896947203 2000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (203839929/1250000000 : ℝ)^4959 ≤ (2034453200977/20000000000000 : ℝ)^3935 := by
    have hnat : (203839929 : ℕ)^4959*20000000000000^3935 ≤ 2034453200977^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203839929 1250000000 2034453200977 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521596619/1000000000 : ℝ)^4959 ≤ (44032886616341/100000000000000 : ℝ)^3935 := by
    have hnat : (521596619 : ℕ)^4959*100000000000000^3935 ≤ 44032886616341^3935*1000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521596619 1000000000 44032886616341 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10509589/19531250 : ℝ), (-203839929/1250000000 : ℝ), (521596619/1000000000 : ℝ)] ![(915896947203/2000000000000 : ℝ), (2034453200977/20000000000000 : ℝ), (44032886616341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10509589/19531250 : ℝ)|^4959 ≤ (915896947203/2000000000000 : ℝ)^3935
        have hw : |(10509589/19531250 : ℝ)|=(10509589/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-203839929/1250000000 : ℝ)|^4959 ≤ (2034453200977/20000000000000 : ℝ)^3935
        have hw : |(-203839929/1250000000 : ℝ)|=(203839929/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(521596619/1000000000 : ℝ)|^4959 ≤ (44032886616341/100000000000000 : ℝ)^3935
        have hw : |(521596619/1000000000 : ℝ)|=(521596619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_6 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380909941/10000000000 : ℝ)*x 0 + (5215965833/10000000000 : ℝ)*x 1 + (-815359703/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380909941/10000000000 : ℝ)^4959 ≤ (9158970272139/20000000000000 : ℝ)^3935 := by
    have hnat : (5380909941 : ℕ)^4959*20000000000000^3935 ≤ 9158970272139^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380909941 10000000000 9158970272139 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215965833/10000000000 : ℝ)^4959 ≤ (44032882818297/100000000000000 : ℝ)^3935 := by
    have hnat : (5215965833 : ℕ)^4959*100000000000000^3935 ≤ 44032882818297^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215965833 10000000000 44032882818297 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (815359703/5000000000 : ℝ)^4959 ≤ (5086132900247/50000000000000 : ℝ)^3935 := by
    have hnat : (815359703 : ℕ)^4959*50000000000000^3935 ≤ 5086132900247^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      815359703 5000000000 5086132900247 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380909941/10000000000 : ℝ), (5215965833/10000000000 : ℝ), (-815359703/5000000000 : ℝ)] ![(9158970272139/20000000000000 : ℝ), (44032882818297/100000000000000 : ℝ), (5086132900247/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380909941/10000000000 : ℝ)|^4959 ≤ (9158970272139/20000000000000 : ℝ)^3935
        have hw : |(5380909941/10000000000 : ℝ)|=(5380909941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215965833/10000000000 : ℝ)|^4959 ≤ (44032882818297/100000000000000 : ℝ)^3935
        have hw : |(5215965833/10000000000 : ℝ)|=(5215965833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-815359703/5000000000 : ℝ)|^4959 ≤ (5086132900247/50000000000000 : ℝ)^3935
        have hw : |(-815359703/5000000000 : ℝ)|=(815359703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_7 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1945160743/5000000000 : ℝ)*x 0 + (4326097713/10000000000 : ℝ)*x 1 + (432609767/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1945160743/5000000000 : ℝ)^4959 ≤ (30429018376867/100000000000000 : ℝ)^3935 := by
    have hnat : (1945160743 : ℕ)^4959*100000000000000^3935 ≤ 30429018376867^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1945160743 5000000000 30429018376867 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4326097713/10000000000 : ℝ)^4959 ≤ (2174093188937/6250000000000 : ℝ)^3935 := by
    have hnat : (4326097713 : ℕ)^4959*6250000000000^3935 ≤ 2174093188937^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326097713 10000000000 2174093188937 6250000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (432609767/1000000000 : ℝ)^4959 ≤ (34785490587259/100000000000000 : ℝ)^3935 := by
    have hnat : (432609767 : ℕ)^4959*100000000000000^3935 ≤ 34785490587259^3935*1000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432609767 1000000000 34785490587259 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1945160743/5000000000 : ℝ), (4326097713/10000000000 : ℝ), (432609767/1000000000 : ℝ)] ![(30429018376867/100000000000000 : ℝ), (2174093188937/6250000000000 : ℝ), (34785490587259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1945160743/5000000000 : ℝ)|^4959 ≤ (30429018376867/100000000000000 : ℝ)^3935
        have hw : |(1945160743/5000000000 : ℝ)|=(1945160743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4326097713/10000000000 : ℝ)|^4959 ≤ (2174093188937/6250000000000 : ℝ)^3935
        have hw : |(4326097713/10000000000 : ℝ)|=(4326097713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(432609767/1000000000 : ℝ)|^4959 ≤ (34785490587259/100000000000000 : ℝ)^3935
        have hw : |(432609767/1000000000 : ℝ)|=(432609767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_8 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1740218721/10000000000 : ℝ)*x 0 + (5079341457/10000000000 : ℝ)*x 1 + (5434948523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1740218721/10000000000 : ℝ)^4959 ≤ (5520229729547/50000000000000 : ℝ)^3935 := by
    have hnat : (1740218721 : ℕ)^4959*50000000000000^3935 ≤ 5520229729547^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740218721 10000000000 5520229729547 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5079341457/10000000000 : ℝ)^4959 ≤ (5323044069859/12500000000000 : ℝ)^3935 := by
    have hnat : (5079341457 : ℕ)^4959*12500000000000^3935 ≤ 5323044069859^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079341457 10000000000 5323044069859 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434948523/10000000000 : ℝ)^4959 ≤ (23187593984913/50000000000000 : ℝ)^3935 := by
    have hnat : (5434948523 : ℕ)^4959*50000000000000^3935 ≤ 23187593984913^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434948523 10000000000 23187593984913 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1740218721/10000000000 : ℝ), (5079341457/10000000000 : ℝ), (5434948523/10000000000 : ℝ)] ![(5520229729547/50000000000000 : ℝ), (5323044069859/12500000000000 : ℝ), (23187593984913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1740218721/10000000000 : ℝ)|^4959 ≤ (5520229729547/50000000000000 : ℝ)^3935
        have hw : |(-1740218721/10000000000 : ℝ)|=(1740218721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5079341457/10000000000 : ℝ)|^4959 ≤ (5323044069859/12500000000000 : ℝ)^3935
        have hw : |(5079341457/10000000000 : ℝ)|=(5079341457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434948523/10000000000 : ℝ)|^4959 ≤ (23187593984913/50000000000000 : ℝ)^3935
        have hw : |(5434948523/10000000000 : ℝ)|=(5434948523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_9 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230807349/10000000000 : ℝ)*x 0 + (-768038919/5000000000 : ℝ)*x 1 + (679368603/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230807349/10000000000 : ℝ)^4959 ≤ (44190836830963/100000000000000 : ℝ)^3935 := by
    have hnat : (5230807349 : ℕ)^4959*100000000000000^3935 ≤ 44190836830963^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230807349 10000000000 44190836830963 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (768038919/5000000000 : ℝ)^4959 ≤ (4716985974539/50000000000000 : ℝ)^3935 := by
    have hnat : (768038919 : ℕ)^4959*50000000000000^3935 ≤ 4716985974539^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768038919 5000000000 4716985974539 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679368603/1250000000 : ℝ)^4959 ≤ (23187595603277/50000000000000 : ℝ)^3935 := by
    have hnat : (679368603 : ℕ)^4959*50000000000000^3935 ≤ 23187595603277^3935*1250000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679368603 1250000000 23187595603277 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230807349/10000000000 : ℝ), (-768038919/5000000000 : ℝ), (679368603/1250000000 : ℝ)] ![(44190836830963/100000000000000 : ℝ), (4716985974539/50000000000000 : ℝ), (23187595603277/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230807349/10000000000 : ℝ)|^4959 ≤ (44190836830963/100000000000000 : ℝ)^3935
        have hw : |(5230807349/10000000000 : ℝ)|=(5230807349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-768038919/5000000000 : ℝ)|^4959 ≤ (4716985974539/50000000000000 : ℝ)^3935
        have hw : |(-768038919/5000000000 : ℝ)|=(768038919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679368603/1250000000 : ℝ)|^4959 ≤ (23187595603277/50000000000000 : ℝ)^3935
        have hw : |(679368603/1250000000 : ℝ)|=(679368603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_10 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1307701959/2500000000 : ℝ)*x 0 + (2717474257/5000000000 : ℝ)*x 1 + (-1920097/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307701959/2500000000 : ℝ)^4959 ≤ (44190842015881/100000000000000 : ℝ)^3935 := by
    have hnat : (1307701959 : ℕ)^4959*100000000000000^3935 ≤ 44190842015881^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307701959 2500000000 44190842015881 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717474257/5000000000 : ℝ)^4959 ≤ (46375187873047/100000000000000 : ℝ)^3935 := by
    have hnat : (2717474257 : ℕ)^4959*100000000000000^3935 ≤ 46375187873047^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717474257 5000000000 46375187873047 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1920097/12500000 : ℝ)^4959 ≤ (9433970107001/100000000000000 : ℝ)^3935 := by
    have hnat : (1920097 : ℕ)^4959*100000000000000^3935 ≤ 9433970107001^3935*12500000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920097 12500000 9433970107001 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1307701959/2500000000 : ℝ), (2717474257/5000000000 : ℝ), (-1920097/12500000 : ℝ)] ![(44190842015881/100000000000000 : ℝ), (46375187873047/100000000000000 : ℝ), (9433970107001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1307701959/2500000000 : ℝ)|^4959 ≤ (44190842015881/100000000000000 : ℝ)^3935
        have hw : |(1307701959/2500000000 : ℝ)|=(1307701959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717474257/5000000000 : ℝ)|^4959 ≤ (46375187873047/100000000000000 : ℝ)^3935
        have hw : |(2717474257/5000000000 : ℝ)|=(2717474257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1920097/12500000 : ℝ)|^4959 ≤ (9433970107001/100000000000000 : ℝ)^3935
        have hw : |(-1920097/12500000 : ℝ)|=(1920097/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_11 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4533384369/10000000000 : ℝ)*x 0 + (2001835871/5000000000 : ℝ)*x 1 + (2001835579/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4533384369/10000000000 : ℝ)^4959 ≤ (36898934205467/100000000000000 : ℝ)^3935 := by
    have hnat : (4533384369 : ℕ)^4959*100000000000000^3935 ≤ 36898934205467^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4533384369 10000000000 36898934205467 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001835871/5000000000 : ℝ)^4959 ≤ (3943816973177/12500000000000 : ℝ)^3935 := by
    have hnat : (2001835871 : ℕ)^4959*12500000000000^3935 ≤ 3943816973177^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001835871 5000000000 3943816973177 12500000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2001835579/5000000000 : ℝ)^4959 ≤ (631010599713/2000000000000 : ℝ)^3935 := by
    have hnat : (2001835579 : ℕ)^4959*2000000000000^3935 ≤ 631010599713^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001835579 5000000000 631010599713 2000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4533384369/10000000000 : ℝ), (2001835871/5000000000 : ℝ), (2001835579/5000000000 : ℝ)] ![(36898934205467/100000000000000 : ℝ), (3943816973177/12500000000000 : ℝ), (631010599713/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4533384369/10000000000 : ℝ)|^4959 ≤ (36898934205467/100000000000000 : ℝ)^3935
        have hw : |(4533384369/10000000000 : ℝ)|=(4533384369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2001835871/5000000000 : ℝ)|^4959 ≤ (3943816973177/12500000000000 : ℝ)^3935
        have hw : |(2001835871/5000000000 : ℝ)|=(2001835871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2001835579/5000000000 : ℝ)|^4959 ≤ (631010599713/2000000000000 : ℝ)^3935
        have hw : |(2001835579/5000000000 : ℝ)|=(2001835579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_12 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1440638833/10000000000 : ℝ)*x 0 + (5537094091/10000000000 : ℝ)*x 1 + (1299042529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1440638833/10000000000 : ℝ)^4959 ≤ (1740271431679/20000000000000 : ℝ)^3935 := by
    have hnat : (1440638833 : ℕ)^4959*20000000000000^3935 ≤ 1740271431679^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1440638833 10000000000 1740271431679 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5537094091/10000000000 : ℝ)^4959 ≤ (47476258154857/100000000000000 : ℝ)^3935 := by
    have hnat : (5537094091 : ℕ)^4959*100000000000000^3935 ≤ 47476258154857^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537094091 10000000000 47476258154857 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1299042529/2500000000 : ℝ)^4959 ≤ (1752895386879/4000000000000 : ℝ)^3935 := by
    have hnat : (1299042529 : ℕ)^4959*4000000000000^3935 ≤ 1752895386879^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299042529 2500000000 1752895386879 4000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1440638833/10000000000 : ℝ), (5537094091/10000000000 : ℝ), (1299042529/2500000000 : ℝ)] ![(1740271431679/20000000000000 : ℝ), (47476258154857/100000000000000 : ℝ), (1752895386879/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1440638833/10000000000 : ℝ)|^4959 ≤ (1740271431679/20000000000000 : ℝ)^3935
        have hw : |(-1440638833/10000000000 : ℝ)|=(1440638833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5537094091/10000000000 : ℝ)|^4959 ≤ (47476258154857/100000000000000 : ℝ)^3935
        have hw : |(5537094091/10000000000 : ℝ)|=(5537094091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1299042529/2500000000 : ℝ)|^4959 ≤ (1752895386879/4000000000000 : ℝ)^3935
        have hw : |(1299042529/2500000000 : ℝ)|=(1299042529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_13 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5394489287/10000000000 : ℝ)*x 0 + (-1638957193/10000000000 : ℝ)*x 1 + (2598085353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5394489287/10000000000 : ℝ)^4959 ≤ (45940541999797/100000000000000 : ℝ)^3935 := by
    have hnat : (5394489287 : ℕ)^4959*100000000000000^3935 ≤ 45940541999797^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394489287 10000000000 45940541999797 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1638957193/10000000000 : ℝ)^4959 ≤ (2559266763209/25000000000000 : ℝ)^3935 := by
    have hnat : (1638957193 : ℕ)^4959*25000000000000^3935 ≤ 2559266763209^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638957193 10000000000 2559266763209 25000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598085353/5000000000 : ℝ)^4959 ≤ (21911195471323/50000000000000 : ℝ)^3935 := by
    have hnat : (2598085353 : ℕ)^4959*50000000000000^3935 ≤ 21911195471323^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598085353 5000000000 21911195471323 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5394489287/10000000000 : ℝ), (-1638957193/10000000000 : ℝ), (2598085353/5000000000 : ℝ)] ![(45940541999797/100000000000000 : ℝ), (2559266763209/25000000000000 : ℝ), (21911195471323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5394489287/10000000000 : ℝ)|^4959 ≤ (45940541999797/100000000000000 : ℝ)^3935
        have hw : |(5394489287/10000000000 : ℝ)|=(5394489287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1638957193/10000000000 : ℝ)|^4959 ≤ (2559266763209/25000000000000 : ℝ)^3935
        have hw : |(-1638957193/10000000000 : ℝ)|=(1638957193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598085353/5000000000 : ℝ)|^4959 ≤ (21911195471323/50000000000000 : ℝ)^3935
        have hw : |(2598085353/5000000000 : ℝ)|=(2598085353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_14 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (84288889/156250000 : ℝ)*x 0 + (2598085559/5000000000 : ℝ)*x 1 + (-1638957169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (84288889/156250000 : ℝ)^4959 ≤ (9188107560689/20000000000000 : ℝ)^3935 := by
    have hnat : (84288889 : ℕ)^4959*20000000000000^3935 ≤ 9188107560689^3935*156250000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84288889 156250000 9188107560689 20000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2598085559/5000000000 : ℝ)^4959 ≤ (2738899707593/6250000000000 : ℝ)^3935 := by
    have hnat : (2598085559 : ℕ)^4959*6250000000000^3935 ≤ 2738899707593^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598085559 5000000000 2738899707593 6250000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1638957169/10000000000 : ℝ)^4959 ≤ (127963335799/1250000000000 : ℝ)^3935 := by
    have hnat : (1638957169 : ℕ)^4959*1250000000000^3935 ≤ 127963335799^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1638957169 10000000000 127963335799 1250000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(84288889/156250000 : ℝ), (2598085559/5000000000 : ℝ), (-1638957169/10000000000 : ℝ)] ![(9188107560689/20000000000000 : ℝ), (2738899707593/6250000000000 : ℝ), (127963335799/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(84288889/156250000 : ℝ)|^4959 ≤ (9188107560689/20000000000000 : ℝ)^3935
        have hw : |(84288889/156250000 : ℝ)|=(84288889/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2598085559/5000000000 : ℝ)|^4959 ≤ (2738899707593/6250000000000 : ℝ)^3935
        have hw : |(2598085559/5000000000 : ℝ)|=(2598085559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1638957169/10000000000 : ℝ)|^4959 ≤ (127963335799/1250000000000 : ℝ)^3935
        have hw : |(-1638957169/10000000000 : ℝ)|=(1638957169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1660_box_15 (p : ℝ) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1915173779/5000000000 : ℝ)*x 0 + (4355183343/10000000000 : ℝ)*x 1 + (1088795831/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1915173779/5000000000 : ℝ)^4959 ≤ (29839036102813/100000000000000 : ℝ)^3935 := by
    have hnat : (1915173779 : ℕ)^4959*100000000000000^3935 ≤ 29839036102813^3935*5000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1915173779 5000000000 29839036102813 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4355183343/10000000000 : ℝ)^4959 ≤ (35080482036711/100000000000000 : ℝ)^3935 := by
    have hnat : (4355183343 : ℕ)^4959*100000000000000^3935 ≤ 35080482036711^3935*10000000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355183343 10000000000 35080482036711 100000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1088795831/2500000000 : ℝ)^4959 ≤ (17540240921921/50000000000000 : ℝ)^3935 := by
    have hnat : (1088795831 : ℕ)^4959*50000000000000^3935 ≤ 17540240921921^3935*2500000000^4959 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1088795831 2500000000 17540240921921 50000000000000 4959 3935 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4959/1024 : ℝ)) 4959 3935 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1915173779/5000000000 : ℝ), (4355183343/10000000000 : ℝ), (1088795831/2500000000 : ℝ)] ![(29839036102813/100000000000000 : ℝ), (35080482036711/100000000000000 : ℝ), (17540240921921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1915173779/5000000000 : ℝ)|^4959 ≤ (29839036102813/100000000000000 : ℝ)^3935
        have hw : |(1915173779/5000000000 : ℝ)|=(1915173779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4355183343/10000000000 : ℝ)|^4959 ≤ (35080482036711/100000000000000 : ℝ)^3935
        have hw : |(4355183343/10000000000 : ℝ)|=(4355183343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1088795831/2500000000 : ℝ)|^4959 ≤ (17540240921921/50000000000000 : ℝ)^3935
        have hw : |(1088795831/2500000000 : ℝ)|=(1088795831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1660_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2031/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(6511/10000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58733/100000 : ℝ) ∧ (81377/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (552/625 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2031/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10721/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2031/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10721/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2031/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10721/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2031/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10721/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2031/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10721/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2031/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10721/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10721/100000 : ℝ) ^ (4955/1024 : ℝ) ≤ (2029725903627017/100000000000000000000 : ℝ) := by
    have hpowers : (10721/100000 : ℝ)^4955 ≤ (2029725903627017/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10721 : ℕ)^4955*100000000000000000000^1024 ≤ 2029725903627017^1024*100000^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10721 100000 2029725903627017 100000000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10721/100000 : ℝ)) (X := (2029725903627017/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2031/12500 : ℝ) ^ (4955/1024 : ℝ) ≤ (1897036098253689/12500000000000000000 : ℝ) := by
    have hpowers : (2031/12500 : ℝ)^4955 ≤ (1897036098253689/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2031 : ℕ)^4955*12500000000000000000^1024 ≤ 1897036098253689^1024*12500^4955 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2031 12500 1897036098253689 12500000000000000000 4955 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2031/12500 : ℝ)) (X := (1897036098253689/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002029725903627017/50000000000000000000 : ℝ) ≤ (10000083891255613/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (50002029725903627017/50000000000000000000 : ℝ)^1024 ≤ (10000083891255613/10000000000000000 : ℝ)^4955 := by
      have hnat : (50002029725903627017 : ℕ)^1024*10000000000000000^4955 ≤ 10000083891255613^4955*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002029725903627017 50000000000000000000 10000083891255613 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083891255613/10000000000000000 : ℝ)) (X := (50002029725903627017/50000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100017206014689656529/100000000000000000000 : ℝ) ≤ (10000355555129213/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (100017206014689656529/100000000000000000000 : ℝ)^1024 ≤ (10000355555129213/10000000000000000 : ℝ)^4955 := by
      have hnat : (100017206014689656529 : ℕ)^1024*10000000000000000^4955 ≤ 10000355555129213^4955*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100017206014689656529 100000000000000000000 10000355555129213 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000355555129213/10000000000000000 : ℝ)) (X := (100017206014689656529/100000000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251897036098253689/6250000000000000000 : ℝ) ≤ (10000627219002813/10000000000000000 : ℝ) ^ (4955/1024 : ℝ) := by
    have hpowers : (6251897036098253689/6250000000000000000 : ℝ)^1024 ≤ (10000627219002813/10000000000000000 : ℝ)^4955 := by
      have hnat : (6251897036098253689 : ℕ)^1024*10000000000000000^4955 ≤ 10000627219002813^4955*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251897036098253689 6250000000000000000 10000627219002813 10000000000000000 1024 4955 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000627219002813/10000000000000000 : ℝ)) (X := (6251897036098253689/6250000000000000000 : ℝ)) (by norm_num) 4955 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2029725903627017/100000000000000000000 : ℝ) ≤ ((55264638650192041851/55270000000000000000 : ℝ)+2*(169789921/345437500000 : ℝ)*(10721/100000 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (55264638650192041851/55270000000000000000 : ℝ)+2*(169789921/345437500000 : ℝ)*(10721/100000 : ℝ)=(10000083891255613/10000000000000000 : ℝ) by norm_num, show 1+2*(2029725903627017/100000000000000000000 : ℝ)=(50002029725903627017/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1897036098253689/12500000000000000000 : ℝ)+(2029725903627017/100000000000000000000 : ℝ) ≤ ((55264638650192041851/55270000000000000000 : ℝ)+(169789921/345437500000 : ℝ)*((2031/12500 : ℝ)+(10721/100000 : ℝ)))^(4955/1024 : ℝ) := by
    rw [show (55264638650192041851/55270000000000000000 : ℝ)+(169789921/345437500000 : ℝ)*((2031/12500 : ℝ)+(10721/100000 : ℝ))=(10000355555129213/10000000000000000 : ℝ) by norm_num, show 1+(1897036098253689/12500000000000000000 : ℝ)+(2029725903627017/100000000000000000000 : ℝ)=(100017206014689656529/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1897036098253689/12500000000000000000 : ℝ) ≤ ((55264638650192041851/55270000000000000000 : ℝ)+2*(169789921/345437500000 : ℝ)*(2031/12500 : ℝ))^(4955/1024 : ℝ) := by
    rw [show (55264638650192041851/55270000000000000000 : ℝ)+2*(169789921/345437500000 : ℝ)*(2031/12500 : ℝ)=(10000627219002813/10000000000000000 : ℝ) by norm_num, show 1+2*(1897036098253689/12500000000000000000 : ℝ)=(6251897036098253689/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (55264638650192041851/55270000000000000000 : ℝ)*(X 1 0+X 2 0)+(169789921/345437500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (2031/12500 : ℝ)) (c := (55264638650192041851/55270000000000000000 : ℝ)) (alpha := (169789921/345437500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (55264638650192041851/55270000000000000000 : ℝ)*(X 0 1+X 2 1)+(169789921/345437500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (2031/12500 : ℝ)) (c := (55264638650192041851/55270000000000000000 : ℝ)) (alpha := (169789921/345437500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (55264638650192041851/55270000000000000000 : ℝ)*(X 0 2+X 1 2)+(169789921/345437500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4955/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (2031/12500 : ℝ)) (c := (55264638650192041851/55270000000000000000 : ℝ)) (alpha := (169789921/345437500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-665819743/5000000000 : ℝ)*X 0 0+(675701963/1250000000 : ℝ)*X 0 1+(1351404243/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((328181969/625000000 : ℝ)*X 1 0+(-1549119447/10000000000 : ℝ)*X 1 1+(2702808073/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((164090979/312500000 : ℝ)*X 2 0+(5405616659/10000000000 : ℝ)*X 2 1+(-774559489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4449303849/10000000000 : ℝ)*X 0 0+(1011731801/2500000000 : ℝ)*X 0 1+(4046927581/10000000000 : ℝ)*X 0 2+(4449303849/10000000000 : ℝ)*X 1 0+(1011731801/2500000000 : ℝ)*X 1 1+(4046927581/10000000000 : ℝ)*X 1 2+(4449303849/10000000000 : ℝ)*X 2 0+(1011731801/2500000000 : ℝ)*X 2 1+(4046927581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-5784691/31250000 : ℝ)*X 0 0+(2607983117/5000000000 : ℝ)*X 0 1+(5215965773/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10509589/19531250 : ℝ)*X 1 0+(-203839929/1250000000 : ℝ)*X 1 1+(521596619/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5380909941/10000000000 : ℝ)*X 2 0+(5215965833/10000000000 : ℝ)*X 2 1+(-815359703/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1945160743/5000000000 : ℝ)*X 0 0+(4326097713/10000000000 : ℝ)*X 0 1+(432609767/1000000000 : ℝ)*X 0 2+(1945160743/5000000000 : ℝ)*X 1 0+(4326097713/10000000000 : ℝ)*X 1 1+(432609767/1000000000 : ℝ)*X 1 2+(1945160743/5000000000 : ℝ)*X 2 0+(4326097713/10000000000 : ℝ)*X 2 1+(432609767/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1740218721/10000000000 : ℝ)*X 0 0+(5079341457/10000000000 : ℝ)*X 0 1+(5434948523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5230807349/10000000000 : ℝ)*X 1 0+(-768038919/5000000000 : ℝ)*X 1 1+(679368603/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1307701959/2500000000 : ℝ)*X 2 0+(2717474257/5000000000 : ℝ)*X 2 1+(-1920097/12500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4533384369/10000000000 : ℝ)*X 0 0+(2001835871/5000000000 : ℝ)*X 0 1+(2001835579/5000000000 : ℝ)*X 0 2+(4533384369/10000000000 : ℝ)*X 1 0+(2001835871/5000000000 : ℝ)*X 1 1+(2001835579/5000000000 : ℝ)*X 1 2+(4533384369/10000000000 : ℝ)*X 2 0+(2001835871/5000000000 : ℝ)*X 2 1+(2001835579/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1440638833/10000000000 : ℝ)*X 0 0+(5537094091/10000000000 : ℝ)*X 0 1+(1299042529/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5394489287/10000000000 : ℝ)*X 1 0+(-1638957193/10000000000 : ℝ)*X 1 1+(2598085353/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((84288889/156250000 : ℝ)*X 2 0+(2598085559/5000000000 : ℝ)*X 2 1+(-1638957169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1915173779/5000000000 : ℝ)*X 0 0+(4355183343/10000000000 : ℝ)*X 0 1+(1088795831/2500000000 : ℝ)*X 0 2+(1915173779/5000000000 : ℝ)*X 1 0+(4355183343/10000000000 : ℝ)*X 1 1+(1088795831/2500000000 : ℝ)*X 1 2+(1915173779/5000000000 : ℝ)*X 2 0+(4355183343/10000000000 : ℝ)*X 2 1+(1088795831/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1660_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-6511/10000 : ℝ) ≤ (-35985075211471818799745187503589/55270000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (748519/100000000000000 : ℝ)*(upper1) + (8930829/20000000000000 : ℝ)*(upper4) + (35969319/100000000000000 : ℝ)*(upper5) + (35558118166187/2000000000000 : ℝ)*(major0) + (35558118166187/2000000000000 : ℝ)*(major1) + (35558118166187/2000000000000 : ℝ)*(major2) + (3880636523/100000000000000 : ℝ)*(sp2) + (444381257/50000000000000 : ℝ)*(sp3) + (1297603241955827/50000000000000 : ℝ)*(sp4) + (1297605047708341/50000000000000 : ℝ)*(sp5) + (1297603733140203/50000000000000 : ℝ)*(sp6) + (196460435482401/20000000000000 : ℝ)*(sp7) + (2431502637/50000000000000 : ℝ)*(sp8) + (625750123/50000000000000 : ℝ)*(sp13) + (24557576654363/2500000000000 : ℝ)*(f.failure) + (40550177295577/1562500000000 : ℝ)*(f.sum) + (958529913057/2763500000000000000000000000 : ℝ)*base66 + (418654110417407863/110540000000000000000000000000000 : ℝ)*base68 + (81655992369972137/110540000000000000000000000000000 : ℝ)*base69 + (225764365991667863/110540000000000000000000000000000 : ℝ)*base72 + (27993294038113/5527000000000000000000000000 : ℝ)*base74 + (37036917987492137/110540000000000000000000000000000 : ℝ)*base75 + (288183055442147863/110540000000000000000000000000000 : ℝ)*base78 + (220242504111947863/110540000000000000000000000000000 : ℝ)*base80 + (2752223450329/2763500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3127149/250000000000000000000 : ℝ)*base89 + (3127149/250000000000000000000 : ℝ)*base91 + (3127149/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58733/100000 : ℝ) ≤ (162316690246521755446813885750251/276350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16165527/100000000000000 : ℝ)*(lower1) + (92026761/100000000000000 : ℝ)*(lower3) + (8629183/20000000000000 : ℝ)*(upper4) + (186972749796489/10000000000000 : ℝ)*(major0) + (186972749796489/10000000000000 : ℝ)*(major1) + (186972749796489/10000000000000 : ℝ)*(major2) + (1343416702086007/50000000000000 : ℝ)*(sp0) + (67171006935171/2500000000000 : ℝ)*(sp1) + (1343416660425381/50000000000000 : ℝ)*(sp2) + (516515736863713/50000000000000 : ℝ)*(sp3) + (1067903627/100000000000000 : ℝ)*(sp5) + (1003057463/12500000000000 : ℝ)*(sp6) + (442483499/12500000000000 : ℝ)*(sp7) + (1985284613/25000000000000 : ℝ)*(sp12) + (1033035013595419/100000000000000 : ℝ)*(f.failure) + (1343420672655233/50000000000000 : ℝ)*(f.sum) + (3201419978109/2763500000000000000000000000 : ℝ)*base65 + (4217494591046738861/552700000000000000000000000000000 : ℝ)*base68 + (4012853546041338861/552700000000000000000000000000000 : ℝ)*base70 + (7538025047500538861/552700000000000000000000000000000 : ℝ)*base72 + (372446508167/86359375000000000000000000 : ℝ)*base73 + (4089395714412338861/552700000000000000000000000000000 : ℝ)*base76 + (5062072143741338861/552700000000000000000000000000000 : ℝ)*base78 + (3715390187172138861/552700000000000000000000000000000 : ℝ)*base80 + (13272026789739/2763500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (141013037/10000000000000000000000 : ℝ)*base89 + (141013037/10000000000000000000000 : ℝ)*base91 + (141013037/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (81377/100000 : ℝ) ≤ (1124455186321116520787053225492671/1381750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (46227563/100000000000000 : ℝ)*(lower3) + (34009253/25000000000000 : ℝ)*(upper4) + (41996949/100000000000000 : ℝ)*(lower5) + (980736965435131/50000000000000 : ℝ)*(major0) + (980736965435131/50000000000000 : ℝ)*(major1) + (980736965435131/50000000000000 : ℝ)*(major2) + (58435163/6250000000000 : ℝ)*(sp0) + (355869221/781250000000 : ℝ)*(sp1) + (72158523/160000000000 : ℝ)*(sp2) + (15936070731/100000000000000 : ℝ)*(sp3) + (2812095136360063/100000000000000 : ℝ)*(sp8) + (175753157503899/6250000000000 : ℝ)*(sp9) + (703012743061449/25000000000000 : ℝ)*(sp10) + (5418547502081/500000000000 : ℝ)*(sp11) + (270931359121733/25000000000000 : ℝ)*(f.failure) + (175756004457667/6250000000000 : ℝ)*(f.sum) + (5863395508731/1381750000000000000000000000 : ℝ)*base65 + (21525152131803167481/2763500000000000000000000000000000 : ℝ)*base67 + (24995564029051667481/2763500000000000000000000000000000 : ℝ)*base69 + (12084703848563167481/2763500000000000000000000000000000 : ℝ)*base71 + (8463327414687/1381750000000000000000000000 : ℝ)*base73 + (8965532588525167481/2763500000000000000000000000000000 : ℝ)*base75 + (24818955268675167481/2763500000000000000000000000000000 : ℝ)*base77 + (14058230551032167481/2763500000000000000000000000000000 : ℝ)*base79 + (15493345416193/5527000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3708659/2500000000000000000000 : ℝ)*base89 + (3708659/2500000000000000000000 : ℝ)*base91 + (3708659/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-552/625 : ℝ) ≤ (-610162612439457835120434775213707/690875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1361831/6250000000000 : ℝ)*(lower0) + (1229771/10000000000000 : ℝ)*(upper3) + (5036427/10000000000000 : ℝ)*(lower4) + (1003037865280581/50000000000000 : ℝ)*(major0) + (1003037865280581/50000000000000 : ℝ)*(major1) + (1003037865280581/50000000000000 : ℝ)*(major2) + (6518613513/100000000000000 : ℝ)*(sp0) + (5921028821/12500000000000 : ℝ)*(sp5) + (1228501967/12500000000000 : ℝ)*(sp7) + (494181229/10000000000000 : ℝ)*(sp8) + (146660547009983/5000000000000 : ℝ)*(sp12) + (183323439524681/6250000000000 : ℝ)*(sp13) + (2933222400625463/100000000000000 : ℝ)*(sp14) + (221671670993559/20000000000000 : ℝ)*(sp15) + (1108368182983531/100000000000000 : ℝ)*(f.failure) + (2933222400625463/100000000000000 : ℝ)*(f.sum) + (9124455515227/2763500000000000000000000000 : ℝ)*base65 + (19744841910312904569/2763500000000000000000000000000000 : ℝ)*base68 + (22830738372571404569/2763500000000000000000000000000000 : ℝ)*base70 + (18507838201037404569/2763500000000000000000000000000000 : ℝ)*base72 + (19692452719117/5527000000000000000000000000 : ℝ)*base73 + (22295066037076404569/2763500000000000000000000000000000 : ℝ)*base76 + (9116373817509404569/2763500000000000000000000000000000 : ℝ)*base78 + (314702959145095431/2763500000000000000000000000000000 : ℝ)*base79 + (10666392736091/5527000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (25022813/10000000000000000000000 : ℝ)*base89 + (25022813/10000000000000000000000 : ℝ)*base91 + (25022813/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1660_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2031/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6511/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58733/100000 : ℝ) else (81377/100000 : ℝ) ≤ X j i ∧ X j i ≤ (552/625 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1660_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1660_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6511/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58733/100000 : ℝ) else (81377/100000 : ℝ) ≤ X j i ∧ X j i ≤ (552/625 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1660_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1660_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1660_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4955/1024 : ℝ) ≤ p) (hpb : p ≤ (4959/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180993623/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5331/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(6511/10000 : ℝ) ≤ X j i ∧ X j i ≤ -(58733/100000 : ℝ) else (81377/100000 : ℝ) ≤ X j i ∧ X j i ≤ (552/625 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1660_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
