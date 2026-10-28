-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1109_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:04:13.183191+00:00
-- url     : https://prove2.me/submissions/6b1d9a90-400b-4cd5-a9e6-3dca0f297ce5

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
theorem support_rectangle_w1109_s3_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1089292327/5000000000 : ℝ)*x 0 + (1086535893/2000000000 : ℝ)*x 1 + (5228873613/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089292327/5000000000 : ℝ)^4151 ≤ (826658554141/6250000000000 : ℝ)^3127 := by
    have hnat : (1089292327 : ℕ)^4151*6250000000000^3127 ≤ 826658554141^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089292327 5000000000 826658554141 6250000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086535893/2000000000 : ℝ)^4151 ≤ (22243802817593/50000000000000 : ℝ)^3127 := by
    have hnat : (1086535893 : ℕ)^4151*50000000000000^3127 ≤ 22243802817593^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086535893 2000000000 22243802817593 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228873613/10000000000 : ℝ)^4151 ≤ (10571464371767/25000000000000 : ℝ)^3127 := by
    have hnat : (5228873613 : ℕ)^4151*25000000000000^3127 ≤ 10571464371767^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228873613 10000000000 10571464371767 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1089292327/5000000000 : ℝ), (1086535893/2000000000 : ℝ), (5228873613/10000000000 : ℝ)] ![(826658554141/6250000000000 : ℝ), (22243802817593/50000000000000 : ℝ), (10571464371767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1089292327/5000000000 : ℝ)|^4151 ≤ (826658554141/6250000000000 : ℝ)^3127
        have hw : |(-1089292327/5000000000 : ℝ)|=(1089292327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086535893/2000000000 : ℝ)|^4151 ≤ (22243802817593/50000000000000 : ℝ)^3127
        have hw : |(1086535893/2000000000 : ℝ)|=(1086535893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228873613/10000000000 : ℝ)|^4151 ≤ (10571464371767/25000000000000 : ℝ)^3127
        have hw : |(5228873613/10000000000 : ℝ)|=(5228873613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s3_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677300627/5000000000 : ℝ)*x 0 + (-228284089/1000000000 : ℝ)*x 1 + (1307218421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677300627/5000000000 : ℝ)^4151 ≤ (4364085963837/10000000000000 : ℝ)^3127 := by
    have hnat : (2677300627 : ℕ)^4151*10000000000000^3127 ≤ 4364085963837^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677300627 5000000000 4364085963837 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228284089/1000000000 : ℝ)^4151 ≤ (14073282094017/100000000000000 : ℝ)^3127 := by
    have hnat : (228284089 : ℕ)^4151*100000000000000^3127 ≤ 14073282094017^3127*1000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228284089 1000000000 14073282094017 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307218421/2500000000 : ℝ)^4151 ≤ (4228585824927/10000000000000 : ℝ)^3127 := by
    have hnat : (1307218421 : ℕ)^4151*10000000000000^3127 ≤ 4228585824927^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307218421 2500000000 4228585824927 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677300627/5000000000 : ℝ), (-228284089/1000000000 : ℝ), (1307218421/2500000000 : ℝ)] ![(4364085963837/10000000000000 : ℝ), (14073282094017/100000000000000 : ℝ), (4228585824927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677300627/5000000000 : ℝ)|^4151 ≤ (4364085963837/10000000000000 : ℝ)^3127
        have hw : |(2677300627/5000000000 : ℝ)|=(2677300627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-228284089/1000000000 : ℝ)|^4151 ≤ (14073282094017/100000000000000 : ℝ)^3127
        have hw : |(-228284089/1000000000 : ℝ)|=(228284089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307218421/2500000000 : ℝ)|^4151 ≤ (4228585824927/10000000000000 : ℝ)^3127
        have hw : |(1307218421/2500000000 : ℝ)|=(1307218421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s3_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669325173/1250000000 : ℝ)*x 0 + (5228873783/10000000000 : ℝ)*x 1 + (-2282840589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669325173/1250000000 : ℝ)^4151 ≤ (10910215261213/25000000000000 : ℝ)^3127 := by
    have hnat : (669325173 : ℕ)^4151*25000000000000^3127 ≤ 10910215261213^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669325173 1250000000 10910215261213 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228873783/10000000000 : ℝ)^4151 ≤ (42285859312059/100000000000000 : ℝ)^3127 := by
    have hnat : (5228873783 : ℕ)^4151*100000000000000^3127 ≤ 42285859312059^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228873783 10000000000 42285859312059 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2282840589/10000000000 : ℝ)^4151 ≤ (439789988461/3125000000000 : ℝ)^3127 := by
    have hnat : (2282840589 : ℕ)^4151*3125000000000^3127 ≤ 439789988461^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2282840589 10000000000 439789988461 3125000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669325173/1250000000 : ℝ), (5228873783/10000000000 : ℝ), (-2282840589/10000000000 : ℝ)] ![(10910215261213/25000000000000 : ℝ), (42285859312059/100000000000000 : ℝ), (439789988461/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669325173/1250000000 : ℝ)|^4151 ≤ (10910215261213/25000000000000 : ℝ)^3127
        have hw : |(669325173/1250000000 : ℝ)|=(669325173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228873783/10000000000 : ℝ)|^4151 ≤ (42285859312059/100000000000000 : ℝ)^3127
        have hw : |(5228873783/10000000000 : ℝ)|=(5228873783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2282840589/10000000000 : ℝ)|^4151 ≤ (439789988461/3125000000000 : ℝ)^3127
        have hw : |(-2282840589/10000000000 : ℝ)|=(2282840589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s3_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091715873/2500000000 : ℝ)*x 0 + (208504677/500000000 : ℝ)*x 1 + (4572936311/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091715873/2500000000 : ℝ)^4151 ≤ (33291687512883/100000000000000 : ℝ)^3127 := by
    have hnat : (1091715873 : ℕ)^4151*100000000000000^3127 ≤ 33291687512883^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091715873 2500000000 33291687512883 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208504677/500000000 : ℝ)^4151 ≤ (31315170581689/100000000000000 : ℝ)^3127 := by
    have hnat : (208504677 : ℕ)^4151*100000000000000^3127 ≤ 31315170581689^3127*500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208504677 500000000 31315170581689 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4572936311/10000000000 : ℝ)^4151 ≤ (35393141891277/100000000000000 : ℝ)^3127 := by
    have hnat : (4572936311 : ℕ)^4151*100000000000000^3127 ≤ 35393141891277^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4572936311 10000000000 35393141891277 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091715873/2500000000 : ℝ), (208504677/500000000 : ℝ), (4572936311/10000000000 : ℝ)] ![(33291687512883/100000000000000 : ℝ), (31315170581689/100000000000000 : ℝ), (35393141891277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091715873/2500000000 : ℝ)|^4151 ≤ (33291687512883/100000000000000 : ℝ)^3127
        have hw : |(1091715873/2500000000 : ℝ)|=(1091715873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208504677/500000000 : ℝ)|^4151 ≤ (31315170581689/100000000000000 : ℝ)^3127
        have hw : |(208504677/500000000 : ℝ)|=(208504677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4572936311/10000000000 : ℝ)|^4151 ≤ (35393141891277/100000000000000 : ℝ)^3127
        have hw : |(4572936311/10000000000 : ℝ)|=(4572936311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s3_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-217860437/1000000000 : ℝ)*x 0 + (40856901/78125000 : ℝ)*x 1 + (339491573/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217860437/1000000000 : ℝ)^4151 ≤ (13226695763371/100000000000000 : ℝ)^3127 := by
    have hnat : (217860437 : ℕ)^4151*100000000000000^3127 ≤ 13226695763371^3127*1000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217860437 1000000000 13226695763371 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40856901/78125000 : ℝ)^4151 ≤ (21147275097071/50000000000000 : ℝ)^3127 := by
    have hnat : (40856901 : ℕ)^4151*50000000000000^3127 ≤ 21147275097071^3127*78125000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40856901 78125000 21147275097071 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339491573/625000000 : ℝ)^4151 ≤ (22239377015573/50000000000000 : ℝ)^3127 := by
    have hnat : (339491573 : ℕ)^4151*50000000000000^3127 ≤ 22239377015573^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339491573 625000000 22239377015573 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217860437/1000000000 : ℝ), (40856901/78125000 : ℝ), (339491573/625000000 : ℝ)] ![(13226695763371/100000000000000 : ℝ), (21147275097071/50000000000000 : ℝ), (22239377015573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217860437/1000000000 : ℝ)|^4151 ≤ (13226695763371/100000000000000 : ℝ)^3127
        have hw : |(-217860437/1000000000 : ℝ)|=(217860437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40856901/78125000 : ℝ)|^4151 ≤ (21147275097071/50000000000000 : ℝ)^3127
        have hw : |(40856901/78125000 : ℝ)|=(40856901/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339491573/625000000 : ℝ)|^4151 ≤ (22239377015573/50000000000000 : ℝ)^3127
        have hw : |(339491573/625000000 : ℝ)|=(339491573/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s3_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303094059/10000000000 : ℝ)*x 0 + (-64995289/312500000 : ℝ)*x 1 + (2715932677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303094059/10000000000 : ℝ)^4151 ≤ (269277986827/625000000000 : ℝ)^3127 := by
    have hnat : (5303094059 : ℕ)^4151*625000000000^3127 ≤ 269277986827^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303094059 10000000000 269277986827 625000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64995289/312500000 : ℝ)^4151 ≤ (497470641253/4000000000000 : ℝ)^3127 := by
    have hnat : (64995289 : ℕ)^4151*4000000000000^3127 ≤ 497470641253^3127*312500000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64995289 312500000 497470641253 4000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715932677/5000000000 : ℝ)^4151 ≤ (44478756052961/100000000000000 : ℝ)^3127 := by
    have hnat : (2715932677 : ℕ)^4151*100000000000000^3127 ≤ 44478756052961^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715932677 5000000000 44478756052961 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303094059/10000000000 : ℝ), (-64995289/312500000 : ℝ), (2715932677/5000000000 : ℝ)] ![(269277986827/625000000000 : ℝ), (497470641253/4000000000000 : ℝ), (44478756052961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303094059/10000000000 : ℝ)|^4151 ≤ (269277986827/625000000000 : ℝ)^3127
        have hw : |(5303094059/10000000000 : ℝ)|=(5303094059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-64995289/312500000 : ℝ)|^4151 ≤ (497470641253/4000000000000 : ℝ)^3127
        have hw : |(-64995289/312500000 : ℝ)|=(64995289/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715932677/5000000000 : ℝ)|^4151 ≤ (44478756052961/100000000000000 : ℝ)^3127
        have hw : |(2715932677/5000000000 : ℝ)|=(2715932677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s3_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5303094109/10000000000 : ℝ)*x 0 + (2715932591/5000000000 : ℝ)*x 1 + (-259981177/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303094109/10000000000 : ℝ)^4151 ≤ (8616895686313/20000000000000 : ℝ)^3127 := by
    have hnat : (5303094109 : ℕ)^4151*20000000000000^3127 ≤ 8616895686313^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303094109 10000000000 8616895686313 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715932591/5000000000 : ℝ)^4151 ≤ (1779150167333/4000000000000 : ℝ)^3127 := by
    have hnat : (2715932591 : ℕ)^4151*4000000000000^3127 ≤ 1779150167333^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715932591 5000000000 1779150167333 4000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259981177/1250000000 : ℝ)^4151 ≤ (3109191841219/25000000000000 : ℝ)^3127 := by
    have hnat : (259981177 : ℕ)^4151*25000000000000^3127 ≤ 3109191841219^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259981177 1250000000 3109191841219 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303094109/10000000000 : ℝ), (2715932591/5000000000 : ℝ), (-259981177/1250000000 : ℝ)] ![(8616895686313/20000000000000 : ℝ), (1779150167333/4000000000000 : ℝ), (3109191841219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303094109/10000000000 : ℝ)|^4151 ≤ (8616895686313/20000000000000 : ℝ)^3127
        have hw : |(5303094109/10000000000 : ℝ)|=(5303094109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715932591/5000000000 : ℝ)|^4151 ≤ (1779150167333/4000000000000 : ℝ)^3127
        have hw : |(2715932591/5000000000 : ℝ)|=(2715932591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259981177/1250000000 : ℝ)|^4151 ≤ (3109191841219/25000000000000 : ℝ)^3127
        have hw : |(-259981177/1250000000 : ℝ)|=(259981177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s3_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2183451217/5000000000 : ℝ)*x 0 + (228566831/500000000 : ℝ)*x 1 + (834340509/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2183451217/5000000000 : ℝ)^4151 ≤ (4161510202007/12500000000000 : ℝ)^3127 := by
    have hnat : (2183451217 : ℕ)^4151*12500000000000^3127 ≤ 4161510202007^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183451217 5000000000 4161510202007 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228566831/500000000 : ℝ)^4151 ≤ (7075341451431/20000000000000 : ℝ)^3127 := by
    have hnat : (228566831 : ℕ)^4151*20000000000000^3127 ≤ 7075341451431^3127*500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228566831 500000000 7075341451431 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (834340509/2000000000 : ℝ)^4151 ≤ (31331211109871/100000000000000 : ℝ)^3127 := by
    have hnat : (834340509 : ℕ)^4151*100000000000000^3127 ≤ 31331211109871^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      834340509 2000000000 31331211109871 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2183451217/5000000000 : ℝ), (228566831/500000000 : ℝ), (834340509/2000000000 : ℝ)] ![(4161510202007/12500000000000 : ℝ), (7075341451431/20000000000000 : ℝ), (31331211109871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2183451217/5000000000 : ℝ)|^4151 ≤ (4161510202007/12500000000000 : ℝ)^3127
        have hw : |(2183451217/5000000000 : ℝ)|=(2183451217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228566831/500000000 : ℝ)|^4151 ≤ (7075341451431/20000000000000 : ℝ)^3127
        have hw : |(228566831/500000000 : ℝ)|=(228566831/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(834340509/2000000000 : ℝ)|^4151 ≤ (31331211109871/100000000000000 : ℝ)^3127
        have hw : |(834340509/2000000000 : ℝ)|=(834340509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16603/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5267/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14847/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16603/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4459/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16603/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4459/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16603/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4459/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16603/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4459/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16603/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4459/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16603/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4459/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4459/50000 : ℝ) ^ (8301/2048 : ℝ) ≤ (222464290911523/4000000000000000000 : ℝ) := by
    have hpowers : (4459/50000 : ℝ)^8301 ≤ (222464290911523/4000000000000000000 : ℝ)^2048 := by
      have hnat : (4459 : ℕ)^8301*4000000000000000000^2048 ≤ 222464290911523^2048*50000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4459 50000 222464290911523 4000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4459/50000 : ℝ)) (X := (222464290911523/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16603/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (172656343032943/250000000000000000 : ℝ) := by
    have hpowers : (16603/100000 : ℝ)^8301 ≤ (172656343032943/250000000000000000 : ℝ)^2048 := by
      have hnat : (16603 : ℕ)^8301*250000000000000000^2048 ≤ 172656343032943^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16603 100000 172656343032943 250000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16603/100000 : ℝ)) (X := (172656343032943/250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000222464290911523/2000000000000000000 : ℝ) ≤ (5000137208704237/5000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (2000222464290911523/2000000000000000000 : ℝ)^2048 ≤ (5000137208704237/5000000000000000 : ℝ)^8301 := by
      have hnat : (2000222464290911523 : ℕ)^2048*5000000000000000^8301 ≤ 5000137208704237^8301*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000222464290911523 2000000000000000000 5000137208704237 5000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000137208704237/5000000000000000 : ℝ)) (X := (2000222464290911523/2000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002984965779438611/4000000000000000000 : ℝ) ≤ (400073623568889/400000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (4002984965779438611/4000000000000000000 : ℝ)^2048 ≤ (400073623568889/400000000000000 : ℝ)^8301 := by
      have hnat : (4002984965779438611 : ℕ)^2048*400000000000000^8301 ≤ 400073623568889^8301*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002984965779438611 4000000000000000000 400073623568889 400000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400073623568889/400000000000000 : ℝ)) (X := (4002984965779438611/4000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (125172656343032943/125000000000000000 : ℝ) ≤ (1250425845129497/1250000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (125172656343032943/125000000000000000 : ℝ)^2048 ≤ (1250425845129497/1250000000000000 : ℝ)^8301 := by
      have hnat : (125172656343032943 : ℕ)^2048*1250000000000000^8301 ≤ 1250425845129497^8301*125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        125172656343032943 125000000000000000 1250425845129497 1250000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250425845129497/1250000000000000 : ℝ)) (X := (125172656343032943/125000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(222464290911523/4000000000000000000 : ℝ) ≤ ((38412087328657029927/38425000000000000000 : ℝ)+2*(1566171813751/768500000000000 : ℝ)*(4459/50000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (38412087328657029927/38425000000000000000 : ℝ)+2*(1566171813751/768500000000000 : ℝ)*(4459/50000 : ℝ)=(5000137208704237/5000000000000000 : ℝ) by norm_num, show 1+2*(222464290911523/4000000000000000000 : ℝ)=(2000222464290911523/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(172656343032943/250000000000000000 : ℝ)+(222464290911523/4000000000000000000 : ℝ) ≤ ((38412087328657029927/38425000000000000000 : ℝ)+(1566171813751/768500000000000 : ℝ)*((16603/100000 : ℝ)+(4459/50000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (38412087328657029927/38425000000000000000 : ℝ)+(1566171813751/768500000000000 : ℝ)*((16603/100000 : ℝ)+(4459/50000 : ℝ))=(400073623568889/400000000000000 : ℝ) by norm_num, show 1+(172656343032943/250000000000000000 : ℝ)+(222464290911523/4000000000000000000 : ℝ)=(4002984965779438611/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(172656343032943/250000000000000000 : ℝ) ≤ ((38412087328657029927/38425000000000000000 : ℝ)+2*(1566171813751/768500000000000 : ℝ)*(16603/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (38412087328657029927/38425000000000000000 : ℝ)+2*(1566171813751/768500000000000 : ℝ)*(16603/100000 : ℝ)=(1250425845129497/1250000000000000 : ℝ) by norm_num, show 1+2*(172656343032943/250000000000000000 : ℝ)=(125172656343032943/125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (38412087328657029927/38425000000000000000 : ℝ)*(X 1 0+X 2 0)+(1566171813751/768500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (4459/50000 : ℝ)) (hi := (16603/100000 : ℝ)) (c := (38412087328657029927/38425000000000000000 : ℝ)) (alpha := (1566171813751/768500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (38412087328657029927/38425000000000000000 : ℝ)*(X 0 1+X 2 1)+(1566171813751/768500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (4459/50000 : ℝ)) (hi := (16603/100000 : ℝ)) (c := (38412087328657029927/38425000000000000000 : ℝ)) (alpha := (1566171813751/768500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (38412087328657029927/38425000000000000000 : ℝ)*(X 0 2+X 1 2)+(1566171813751/768500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (4459/50000 : ℝ)) (hi := (16603/100000 : ℝ)) (c := (38412087328657029927/38425000000000000000 : ℝ)) (alpha := (1566171813751/768500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1089292327/5000000000 : ℝ)*X 0 0+(1086535893/2000000000 : ℝ)*X 0 1+(5228873613/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677300627/5000000000 : ℝ)*X 1 0+(-228284089/1000000000 : ℝ)*X 1 1+(1307218421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669325173/1250000000 : ℝ)*X 2 0+(5228873783/10000000000 : ℝ)*X 2 1+(-2282840589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091715873/2500000000 : ℝ)*X 0 0+(208504677/500000000 : ℝ)*X 0 1+(4572936311/10000000000 : ℝ)*X 0 2+(1091715873/2500000000 : ℝ)*X 1 0+(208504677/500000000 : ℝ)*X 1 1+(4572936311/10000000000 : ℝ)*X 1 2+(1091715873/2500000000 : ℝ)*X 2 0+(208504677/500000000 : ℝ)*X 2 1+(4572936311/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-217860437/1000000000 : ℝ)*X 0 0+(40856901/78125000 : ℝ)*X 0 1+(339491573/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303094059/10000000000 : ℝ)*X 1 0+(-64995289/312500000 : ℝ)*X 1 1+(2715932677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5303094109/10000000000 : ℝ)*X 2 0+(2715932591/5000000000 : ℝ)*X 2 1+(-259981177/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2183451217/5000000000 : ℝ)*X 0 0+(228566831/500000000 : ℝ)*X 0 1+(834340509/2000000000 : ℝ)*X 0 2+(2183451217/5000000000 : ℝ)*X 1 0+(228566831/500000000 : ℝ)*X 1 1+(834340509/2000000000 : ℝ)*X 1 2+(2183451217/5000000000 : ℝ)*X 2 0+(228566831/500000000 : ℝ)*X 2 1+(834340509/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7067625894920993723811/768500000000000000000000000 : ℝ) := by norm_num
    linear_combination (2355296591/100000000000000 : ℝ)*(base19) + (2209749391/100000000000000 : ℝ)*(base23) + (141722071/100000000000000 : ℝ)*(lower2) + (3955931/2500000000000 : ℝ)*(upper3) + (14281337/5000000000000 : ℝ)*(upper5) + (73891204133089/2000000000000 : ℝ)*(major0) + (73891204133089/2000000000000 : ℝ)*(major1) + (73891204133089/2000000000000 : ℝ)*(major2) + (4906672066343471/100000000000000 : ℝ)*(sp0) + (2453359495519843/50000000000000 : ℝ)*(sp1) + (4906719136586887/100000000000000 : ℝ)*(sp2) + (248237849049949/10000000000000 : ℝ)*(sp3) + (49279992807/100000000000000 : ℝ)*(sp4) + (5067479527/25000000000000 : ℝ)*(sp7) + (1241199380208799/50000000000000 : ℝ)*(f.failure) + (2453360673168139/50000000000000 : ℝ)*(f.sum) + (3104797194271/768500000000000000000000000 : ℝ)*base65 + (217668172820445497/76850000000000000000000000000000 : ℝ)*base68 + (49811578834745497/76850000000000000000000000000000 : ℝ)*base70 + (303766306843304503/76850000000000000000000000000000 : ℝ)*base71 + (1958797934969/768500000000000000000000000 : ℝ)*base73 + (919693751829004503/76850000000000000000000000000000 : ℝ)*base75 + (92652796619904503/76850000000000000000000000000000 : ℝ)*base77 + (238382230368945497/76850000000000000000000000000000 : ℝ)*base80 + (9213850740319/1537000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (33256647/5000000000000000000000 : ℝ)*base90 + (33256647/5000000000000000000000 : ℝ)*base92 + (33256647/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99281201250382444415251767/12007812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (303158947/20000000000000 : ℝ)*(base19) + (365971579/20000000000000 : ℝ)*(base23) + (13152543/6250000000000 : ℝ)*(upper3) + (6420283/5000000000000 : ℝ)*(lower4) + (29659711/25000000000000 : ℝ)*(upper5) + (23276024213057/625000000000 : ℝ)*(major0) + (23276024213057/625000000000 : ℝ)*(major1) + (23276024213057/625000000000 : ℝ)*(major2) + (28276581979/100000000000000 : ℝ)*(sp1) + (3088098733/10000000000000 : ℝ)*(sp2) + (989207563529127/20000000000000 : ℝ)*(sp4) + (123650200631723/2500000000000 : ℝ)*(sp5) + (4946005106800409/100000000000000 : ℝ)*(sp6) + (2502289654930909/100000000000000 : ℝ)*(sp7) + (2502289654930909/100000000000000 : ℝ)*(f.failure) + (989207563529127/20000000000000 : ℝ)*(f.sum) + (14553611882491/1921250000000000000000000000 : ℝ)*base65 + (137010771302430661/24015625000000000000000000000000 : ℝ)*base68 + (130061565915473143/12007812500000000000000000000000 : ℝ)*base70 + (185667498808444339/24015625000000000000000000000000 : ℝ)*base71 + (8234815431237/3842500000000000000000000000 : ℝ)*base73 + (82258423958691893/12007812500000000000000000000000 : ℝ)*base76 + (1153129110891327/750488281250000000000000000000 : ℝ)*base77 + (244868678759868161/24015625000000000000000000000000 : ℝ)*base80 + (4625853839511/7685000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (45595477/10000000000000000000000 : ℝ)*base90 + (45595477/10000000000000000000000 : ℝ)*base92 + (45595477/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1109_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16603/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14847/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1109_s4_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090932437/5000000000 : ℝ)*x 0 + (21107537/39062500 : ℝ)*x 1 + (656984869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090932437/5000000000 : ℝ)^4151 ≤ (3313244902991/25000000000000 : ℝ)^3127 := by
    have hnat : (1090932437 : ℕ)^4151*25000000000000^3127 ≤ 3313244902991^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090932437 5000000000 3313244902991 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21107537/39062500 : ℝ)^4151 ≤ (11042752289183/25000000000000 : ℝ)^3127 := by
    have hnat : (21107537 : ℕ)^4151*25000000000000^3127 ≤ 11042752289183^3127*39062500^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21107537 39062500 11042752289183 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656984869/1250000000 : ℝ)^4151 ≤ (4257601121759/10000000000000 : ℝ)^3127 := by
    have hnat : (656984869 : ℕ)^4151*10000000000000^3127 ≤ 4257601121759^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656984869 1250000000 4257601121759 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090932437/5000000000 : ℝ), (21107537/39062500 : ℝ), (656984869/1250000000 : ℝ)] ![(3313244902991/25000000000000 : ℝ), (11042752289183/25000000000000 : ℝ), (4257601121759/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090932437/5000000000 : ℝ)|^4151 ≤ (3313244902991/25000000000000 : ℝ)^3127
        have hw : |(-1090932437/5000000000 : ℝ)|=(1090932437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(21107537/39062500 : ℝ)|^4151 ≤ (11042752289183/25000000000000 : ℝ)^3127
        have hw : |(21107537/39062500 : ℝ)|=(21107537/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656984869/1250000000 : ℝ)|^4151 ≤ (4257601121759/10000000000000 : ℝ)^3127
        have hw : |(656984869/1250000000 : ℝ)|=(656984869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s4_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83552299/156250000 : ℝ)*x 0 + (-1128462271/5000000000 : ℝ)*x 1 + (5255879557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83552299/156250000 : ℝ)^4151 ≤ (2722649627913/6250000000000 : ℝ)^3127 := by
    have hnat : (83552299 : ℕ)^4151*6250000000000^3127 ≤ 2722649627913^3127*156250000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83552299 156250000 2722649627913 6250000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128462271/5000000000 : ℝ)^4151 ≤ (1386158821297/10000000000000 : ℝ)^3127 := by
    have hnat : (1128462271 : ℕ)^4151*10000000000000^3127 ≤ 1386158821297^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128462271 5000000000 1386158821297 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255879557/10000000000 : ℝ)^4151 ≤ (42576017723377/100000000000000 : ℝ)^3127 := by
    have hnat : (5255879557 : ℕ)^4151*100000000000000^3127 ≤ 42576017723377^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255879557 10000000000 42576017723377 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83552299/156250000 : ℝ), (-1128462271/5000000000 : ℝ), (5255879557/10000000000 : ℝ)] ![(2722649627913/6250000000000 : ℝ), (1386158821297/10000000000000 : ℝ), (42576017723377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83552299/156250000 : ℝ)|^4151 ≤ (2722649627913/6250000000000 : ℝ)^3127
        have hw : |(83552299/156250000 : ℝ)|=(83552299/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128462271/5000000000 : ℝ)|^4151 ≤ (1386158821297/10000000000000 : ℝ)^3127
        have hw : |(-1128462271/5000000000 : ℝ)|=(1128462271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255879557/10000000000 : ℝ)|^4151 ≤ (42576017723377/100000000000000 : ℝ)^3127
        have hw : |(5255879557/10000000000 : ℝ)|=(5255879557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s4_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347346443/10000000000 : ℝ)*x 0 + (1313969921/2500000000 : ℝ)*x 1 + (-1128462647/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347346443/10000000000 : ℝ)^4151 ≤ (21781193276151/50000000000000 : ℝ)^3127 := by
    have hnat : (5347346443 : ℕ)^4151*50000000000000^3127 ≤ 21781193276151^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347346443 10000000000 21781193276151 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313969921/2500000000 : ℝ)^4151 ≤ (8515203817811/20000000000000 : ℝ)^3127 := by
    have hnat : (1313969921 : ℕ)^4151*20000000000000^3127 ≤ 8515203817811^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313969921 2500000000 8515203817811 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1128462647/5000000000 : ℝ)^4151 ≤ (6930797172037/50000000000000 : ℝ)^3127 := by
    have hnat : (1128462647 : ℕ)^4151*50000000000000^3127 ≤ 6930797172037^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128462647 5000000000 6930797172037 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347346443/10000000000 : ℝ), (1313969921/2500000000 : ℝ), (-1128462647/5000000000 : ℝ)] ![(21781193276151/50000000000000 : ℝ), (8515203817811/20000000000000 : ℝ), (6930797172037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347346443/10000000000 : ℝ)|^4151 ≤ (21781193276151/50000000000000 : ℝ)^3127
        have hw : |(5347346443/10000000000 : ℝ)|=(5347346443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313969921/2500000000 : ℝ)|^4151 ≤ (8515203817811/20000000000000 : ℝ)^3127
        have hw : |(1313969921/2500000000 : ℝ)|=(1313969921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1128462647/5000000000 : ℝ)|^4151 ≤ (6930797172037/50000000000000 : ℝ)^3127
        have hw : |(-1128462647/5000000000 : ℝ)|=(1128462647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s4_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4368817837/10000000000 : ℝ)*x 0 + (4225336671/10000000000 : ℝ)*x 1 + (4517183777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4368817837/10000000000 : ℝ)^4151 ≤ (666229348263/2000000000000 : ℝ)^3127 := by
    have hnat : (4368817837 : ℕ)^4151*2000000000000^3127 ≤ 666229348263^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4368817837 10000000000 666229348263 2000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4225336671/10000000000 : ℝ)^4151 ≤ (31867057809013/100000000000000 : ℝ)^3127 := by
    have hnat : (4225336671 : ℕ)^4151*100000000000000^3127 ≤ 31867057809013^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225336671 10000000000 31867057809013 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4517183777/10000000000 : ℝ)^4151 ≤ (8705368690463/25000000000000 : ℝ)^3127 := by
    have hnat : (4517183777 : ℕ)^4151*25000000000000^3127 ≤ 8705368690463^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4517183777 10000000000 8705368690463 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4368817837/10000000000 : ℝ), (4225336671/10000000000 : ℝ), (4517183777/10000000000 : ℝ)] ![(666229348263/2000000000000 : ℝ), (31867057809013/100000000000000 : ℝ), (8705368690463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4368817837/10000000000 : ℝ)|^4151 ≤ (666229348263/2000000000000 : ℝ)^3127
        have hw : |(4368817837/10000000000 : ℝ)|=(4368817837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4225336671/10000000000 : ℝ)|^4151 ≤ (31867057809013/100000000000000 : ℝ)^3127
        have hw : |(4225336671/10000000000 : ℝ)|=(4225336671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4517183777/10000000000 : ℝ)|^4151 ≤ (8705368690463/25000000000000 : ℝ)^3127
        have hw : |(4517183777/10000000000 : ℝ)|=(4517183777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s4_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1090935849/5000000000 : ℝ)*x 0 + (2628152471/5000000000 : ℝ)*x 1 + (675387781/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1090935849/5000000000 : ℝ)^4151 ≤ (6626517317831/50000000000000 : ℝ)^3127 := by
    have hnat : (1090935849 : ℕ)^4151*50000000000000^3127 ≤ 6626517317831^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090935849 5000000000 6626517317831 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2628152471/5000000000 : ℝ)^4151 ≤ (21290296052601/50000000000000 : ℝ)^3127 := by
    have hnat : (2628152471 : ℕ)^4151*50000000000000^3127 ≤ 21290296052601^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628152471 5000000000 21290296052601 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675387781/1250000000 : ℝ)^4151 ≤ (44166373250227/100000000000000 : ℝ)^3127 := by
    have hnat : (675387781 : ℕ)^4151*100000000000000^3127 ≤ 44166373250227^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675387781 1250000000 44166373250227 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1090935849/5000000000 : ℝ), (2628152471/5000000000 : ℝ), (675387781/1250000000 : ℝ)] ![(6626517317831/50000000000000 : ℝ), (21290296052601/50000000000000 : ℝ), (44166373250227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1090935849/5000000000 : ℝ)|^4151 ≤ (6626517317831/50000000000000 : ℝ)^3127
        have hw : |(-1090935849/5000000000 : ℝ)|=(1090935849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2628152471/5000000000 : ℝ)|^4151 ≤ (21290296052601/50000000000000 : ℝ)^3127
        have hw : |(2628152471/5000000000 : ℝ)|=(2628152471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675387781/1250000000 : ℝ)|^4151 ≤ (44166373250227/100000000000000 : ℝ)^3127
        have hw : |(675387781/1250000000 : ℝ)|=(675387781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s4_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655016767/5000000000 : ℝ)*x 0 + (-2109702437/10000000000 : ℝ)*x 1 + (5403102363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655016767/5000000000 : ℝ)^4151 ≤ (2697458469209/6250000000000 : ℝ)^3127 := by
    have hnat : (2655016767 : ℕ)^4151*6250000000000^3127 ≤ 2697458469209^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655016767 5000000000 2697458469209 6250000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109702437/10000000000 : ℝ)^4151 ≤ (12674289980029/100000000000000 : ℝ)^3127 := by
    have hnat : (2109702437 : ℕ)^4151*100000000000000^3127 ≤ 12674289980029^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109702437 10000000000 12674289980029 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403102363/10000000000 : ℝ)^4151 ≤ (22083187249051/50000000000000 : ℝ)^3127 := by
    have hnat : (5403102363 : ℕ)^4151*50000000000000^3127 ≤ 22083187249051^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403102363 10000000000 22083187249051 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655016767/5000000000 : ℝ), (-2109702437/10000000000 : ℝ), (5403102363/10000000000 : ℝ)] ![(2697458469209/6250000000000 : ℝ), (12674289980029/100000000000000 : ℝ), (22083187249051/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655016767/5000000000 : ℝ)|^4151 ≤ (2697458469209/6250000000000 : ℝ)^3127
        have hw : |(2655016767/5000000000 : ℝ)|=(2655016767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2109702437/10000000000 : ℝ)|^4151 ≤ (12674289980029/100000000000000 : ℝ)^3127
        have hw : |(-2109702437/10000000000 : ℝ)|=(2109702437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403102363/10000000000 : ℝ)|^4151 ≤ (22083187249051/50000000000000 : ℝ)^3127
        have hw : |(5403102363/10000000000 : ℝ)|=(5403102363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s4_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531003371/1000000000 : ℝ)*x 0 + (216124091/400000000 : ℝ)*x 1 + (-1054851159/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531003371/1000000000 : ℝ)^4151 ≤ (431593374063/1000000000000 : ℝ)^3127 := by
    have hnat : (531003371 : ℕ)^4151*1000000000000^3127 ≤ 431593374063^3127*1000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531003371 1000000000 431593374063 1000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216124091/400000000 : ℝ)^4151 ≤ (22083186771603/50000000000000 : ℝ)^3127 := by
    have hnat : (216124091 : ℕ)^4151*50000000000000^3127 ≤ 22083186771603^3127*400000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216124091 400000000 22083186771603 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054851159/5000000000 : ℝ)^4151 ≤ (12674289031011/100000000000000 : ℝ)^3127 := by
    have hnat : (1054851159 : ℕ)^4151*100000000000000^3127 ≤ 12674289031011^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054851159 5000000000 12674289031011 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531003371/1000000000 : ℝ), (216124091/400000000 : ℝ), (-1054851159/5000000000 : ℝ)] ![(431593374063/1000000000000 : ℝ), (22083186771603/50000000000000 : ℝ), (12674289031011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531003371/1000000000 : ℝ)|^4151 ≤ (431593374063/1000000000000 : ℝ)^3127
        have hw : |(531003371/1000000000 : ℝ)|=(531003371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216124091/400000000 : ℝ)|^4151 ≤ (22083186771603/50000000000000 : ℝ)^3127
        have hw : |(216124091/400000000 : ℝ)|=(216124091/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054851159/5000000000 : ℝ)|^4151 ≤ (12674289031011/100000000000000 : ℝ)^3127
        have hw : |(-1054851159/5000000000 : ℝ)|=(1054851159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s4_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273052037/625000000 : ℝ)*x 0 + (45163421/100000000 : ℝ)*x 1 + (4226181989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273052037/625000000 : ℝ)^4151 ≤ (6662323351867/20000000000000 : ℝ)^3127 := by
    have hnat : (273052037 : ℕ)^4151*20000000000000^3127 ≤ 6662323351867^3127*625000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273052037 625000000 6662323351867 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (45163421/100000000 : ℝ)^4151 ≤ (34812862118529/100000000000000 : ℝ)^3127 := by
    have hnat : (45163421 : ℕ)^4151*100000000000000^3127 ≤ 34812862118529^3127*100000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      45163421 100000000 34812862118529 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226181989/10000000000 : ℝ)^4151 ≤ (6375104222223/20000000000000 : ℝ)^3127 := by
    have hnat : (4226181989 : ℕ)^4151*20000000000000^3127 ≤ 6375104222223^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226181989 10000000000 6375104222223 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273052037/625000000 : ℝ), (45163421/100000000 : ℝ), (4226181989/10000000000 : ℝ)] ![(6662323351867/20000000000000 : ℝ), (34812862118529/100000000000000 : ℝ), (6375104222223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273052037/625000000 : ℝ)|^4151 ≤ (6662323351867/20000000000000 : ℝ)^3127
        have hw : |(273052037/625000000 : ℝ)|=(273052037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(45163421/100000000 : ℝ)|^4151 ≤ (34812862118529/100000000000000 : ℝ)^3127
        have hw : |(45163421/100000000 : ℝ)|=(45163421/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226181989/10000000000 : ℝ)|^4151 ≤ (6375104222223/20000000000000 : ℝ)^3127
        have hw : |(4226181989/10000000000 : ℝ)|=(4226181989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14847/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11111/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14847/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5267/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14847/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5267/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14847/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5267/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14847/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5267/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14847/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5267/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14847/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5267/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5267/50000 : ℝ) ^ (8301/2048 : ℝ) ≤ (341352507713051/3125000000000000000 : ℝ) := by
    have hpowers : (5267/50000 : ℝ)^8301 ≤ (341352507713051/3125000000000000000 : ℝ)^2048 := by
      have hnat : (5267 : ℕ)^8301*3125000000000000000^2048 ≤ 341352507713051^2048*50000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5267 50000 341352507713051 3125000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5267/50000 : ℝ)) (X := (341352507713051/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14847/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (2195013775773843/5000000000000000000 : ℝ) := by
    have hpowers : (14847/100000 : ℝ)^8301 ≤ (2195013775773843/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14847 : ℕ)^8301*5000000000000000000^2048 ≤ 2195013775773843^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14847 100000 2195013775773843 5000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14847/100000 : ℝ)) (X := (2195013775773843/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562841352507713051/1562500000000000000 : ℝ) ≤ (10000538948016707/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (1562841352507713051/1562500000000000000 : ℝ)^2048 ≤ (10000538948016707/10000000000000000 : ℝ)^8301 := by
      have hnat : (1562841352507713051 : ℕ)^2048*10000000000000000^8301 ≤ 10000538948016707^8301*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562841352507713051 1562500000000000000 10000538948016707 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538948016707/10000000000000000 : ℝ)) (X := (1562841352507713051/1562500000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25013705888940573623/25000000000000000000 : ℝ) ≤ (125016903906971/125000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (25013705888940573623/25000000000000000000 : ℝ)^2048 ≤ (125016903906971/125000000000000 : ℝ)^8301 := by
      have hnat : (25013705888940573623 : ℕ)^2048*125000000000000^8301 ≤ 125016903906971^8301*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013705888940573623 25000000000000000000 125016903906971 125000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125016903906971/125000000000000 : ℝ)) (X := (25013705888940573623/25000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502195013775773843/2500000000000000000 : ℝ) ≤ (10002165677098653/10000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (2502195013775773843/2500000000000000000 : ℝ)^2048 ≤ (10002165677098653/10000000000000000 : ℝ)^8301 := by
      have hnat : (2502195013775773843 : ℕ)^2048*10000000000000000^8301 ≤ 10002165677098653^8301*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502195013775773843 2500000000000000000 10002165677098653 10000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002165677098653/10000000000000000 : ℝ)) (X := (2502195013775773843/2500000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(341352507713051/3125000000000000000 : ℝ) ≤ ((43115188518646838127/43130000000000000000 : ℝ)+2*(813364540973/431300000000000 : ℝ)*(5267/50000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (43115188518646838127/43130000000000000000 : ℝ)+2*(813364540973/431300000000000 : ℝ)*(5267/50000 : ℝ)=(10000538948016707/10000000000000000 : ℝ) by norm_num, show 1+2*(341352507713051/3125000000000000000 : ℝ)=(1562841352507713051/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2195013775773843/5000000000000000000 : ℝ)+(341352507713051/3125000000000000000 : ℝ) ≤ ((43115188518646838127/43130000000000000000 : ℝ)+(813364540973/431300000000000 : ℝ)*((14847/100000 : ℝ)+(5267/50000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (43115188518646838127/43130000000000000000 : ℝ)+(813364540973/431300000000000 : ℝ)*((14847/100000 : ℝ)+(5267/50000 : ℝ))=(125016903906971/125000000000000 : ℝ) by norm_num, show 1+(2195013775773843/5000000000000000000 : ℝ)+(341352507713051/3125000000000000000 : ℝ)=(25013705888940573623/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2195013775773843/5000000000000000000 : ℝ) ≤ ((43115188518646838127/43130000000000000000 : ℝ)+2*(813364540973/431300000000000 : ℝ)*(14847/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (43115188518646838127/43130000000000000000 : ℝ)+2*(813364540973/431300000000000 : ℝ)*(14847/100000 : ℝ)=(10002165677098653/10000000000000000 : ℝ) by norm_num, show 1+2*(2195013775773843/5000000000000000000 : ℝ)=(2502195013775773843/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43115188518646838127/43130000000000000000 : ℝ)*(X 1 0+X 2 0)+(813364540973/431300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (14847/100000 : ℝ)) (c := (43115188518646838127/43130000000000000000 : ℝ)) (alpha := (813364540973/431300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43115188518646838127/43130000000000000000 : ℝ)*(X 0 1+X 2 1)+(813364540973/431300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (14847/100000 : ℝ)) (c := (43115188518646838127/43130000000000000000 : ℝ)) (alpha := (813364540973/431300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43115188518646838127/43130000000000000000 : ℝ)*(X 0 2+X 1 2)+(813364540973/431300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (5267/50000 : ℝ)) (hi := (14847/100000 : ℝ)) (c := (43115188518646838127/43130000000000000000 : ℝ)) (alpha := (813364540973/431300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1090932437/5000000000 : ℝ)*X 0 0+(21107537/39062500 : ℝ)*X 0 1+(656984869/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((83552299/156250000 : ℝ)*X 1 0+(-1128462271/5000000000 : ℝ)*X 1 1+(5255879557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347346443/10000000000 : ℝ)*X 2 0+(1313969921/2500000000 : ℝ)*X 2 1+(-1128462647/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4368817837/10000000000 : ℝ)*X 0 0+(4225336671/10000000000 : ℝ)*X 0 1+(4517183777/10000000000 : ℝ)*X 0 2+(4368817837/10000000000 : ℝ)*X 1 0+(4225336671/10000000000 : ℝ)*X 1 1+(4517183777/10000000000 : ℝ)*X 1 2+(4368817837/10000000000 : ℝ)*X 2 0+(4225336671/10000000000 : ℝ)*X 2 1+(4517183777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1090935849/5000000000 : ℝ)*X 0 0+(2628152471/5000000000 : ℝ)*X 0 1+(675387781/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2655016767/5000000000 : ℝ)*X 1 0+(-2109702437/10000000000 : ℝ)*X 1 1+(5403102363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531003371/1000000000 : ℝ)*X 2 0+(216124091/400000000 : ℝ)*X 2 1+(-1054851159/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((273052037/625000000 : ℝ)*X 0 0+(45163421/100000000 : ℝ)*X 0 1+(4226181989/10000000000 : ℝ)*X 0 2+(273052037/625000000 : ℝ)*X 1 0+(45163421/100000000 : ℝ)*X 1 1+(4226181989/10000000000 : ℝ)*X 1 2+(273052037/625000000 : ℝ)*X 2 0+(45163421/100000000 : ℝ)*X 2 1+(4226181989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1617516344749600968877227141/1078250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2254942321/100000000000000 : ℝ)*(base19) + (1970440823/100000000000000 : ℝ)*(base23) + (355080701/100000000000000 : ℝ)*(upper2) + (786332153/100000000000000 : ℝ)*(upper3) + (37852149/100000000000000 : ℝ)*(upper4) + (2549855537947961/50000000000000 : ℝ)*(major0) + (2549855537947961/50000000000000 : ℝ)*(major1) + (2549855537947961/50000000000000 : ℝ)*(major2) + (67728463517001/1000000000000 : ℝ)*(sp0) + (6772891181676749/100000000000000 : ℝ)*(sp1) + (6772891466178247/100000000000000 : ℝ)*(sp2) + (1713243196622771/50000000000000 : ℝ)*(sp3) + (4708491897/10000000000000 : ℝ)*(sp4) + (10567980713/25000000000000 : ℝ)*(sp7) + (428316083146049/12500000000000 : ℝ)*(f.failure) + (677289343661907/10000000000000 : ℝ)*(f.sum) + (1728846845077/673906250000000000000000000 : ℝ)*base66 + (2512358541520990953/2156500000000000000000000000000000 : ℝ)*base68 + (16635466166570990953/2156500000000000000000000000000000 : ℝ)*base70 + (12111236547459009047/2156500000000000000000000000000000 : ℝ)*base71 + (63586029019477/10782500000000000000000000000 : ℝ)*base74 + (15212565270335490953/2156500000000000000000000000000000 : ℝ)*base76 + (2500827600288509047/2156500000000000000000000000000000 : ℝ)*base77 + (20183014999272990953/2156500000000000000000000000000000 : ℝ)*base80 + (29322901659127/10782500000000000000000000000 : ℝ)*base82 + (15255897/1250000000000000000000 : ℝ)*base90 + (15255897/1250000000000000000000 : ℝ)*base92 + (15255897/1250000000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69508484916256049619272559/33695312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (24716101/12500000000000 : ℝ)*(base19) + (111944629/20000000000000 : ℝ)*(base23) + (49753459/50000000000000 : ℝ)*(upper3) + (4532469/10000000000000 : ℝ)*(lower4) + (38391239/25000000000000 : ℝ)*(upper5) + (40072229909659/781250000000 : ℝ)*(major0) + (40072229909659/781250000000 : ℝ)*(major1) + (40072229909659/781250000000 : ℝ)*(major2) + (4736110299/100000000000000 : ℝ)*(sp1) + (11972960083/100000000000000 : ℝ)*(sp2) + (6812117801552381/100000000000000 : ℝ)*(sp4) + (272484514708531/4000000000000 : ℝ)*(sp5) + (212878289652161/3125000000000 : ℝ)*(sp6) + (172318649327927/5000000000000 : ℝ)*(sp7) + (172318649327927/5000000000000 : ℝ)*(f.failure) + (6812117801552381/100000000000000 : ℝ)*(f.sum) + (55561290640367/10782500000000000000000000000 : ℝ)*base66 + (19570683176523409/16847656250000000000000000000000 : ℝ)*base67 + (574839969343687443/33695312500000000000000000000000 : ℝ)*base69 + (6121860909280277/2105957031250000000000000000000 : ℝ)*base72 + (91718437949859/21565000000000000000000000000 : ℝ)*base74 + (66061847902749943/33695312500000000000000000000000 : ℝ)*base75 + (921071003125296761/67390625000000000000000000000000 : ℝ)*base77 + (244379256347499943/33695312500000000000000000000000 : ℝ)*base79 + (5470966711717/10782500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (592031/500000000000000000000 : ℝ)*base90 + (592031/500000000000000000000 : ℝ)*base92 + (592031/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1109_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14847/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5267/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1109_s5_0 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182579699/10000000000 : ℝ)*x 0 + (5395792049/10000000000 : ℝ)*x 1 + (2631573693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182579699/10000000000 : ℝ)^4151 ≤ (6629371869601/50000000000000 : ℝ)^3127 := by
    have hnat : (2182579699 : ℕ)^4151*50000000000000^3127 ≤ 6629371869601^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182579699 10000000000 6629371869601 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395792049/10000000000 : ℝ)^4151 ≤ (44087067193603/100000000000000 : ℝ)^3127 := by
    have hnat : (5395792049 : ℕ)^4151*100000000000000^3127 ≤ 44087067193603^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395792049 10000000000 44087067193603 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2631573693/5000000000 : ℝ)^4151 ≤ (8530837809721/20000000000000 : ℝ)^3127 := by
    have hnat : (2631573693 : ℕ)^4151*20000000000000^3127 ≤ 8530837809721^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631573693 5000000000 8530837809721 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182579699/10000000000 : ℝ), (5395792049/10000000000 : ℝ), (2631573693/5000000000 : ℝ)] ![(6629371869601/50000000000000 : ℝ), (44087067193603/100000000000000 : ℝ), (8530837809721/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182579699/10000000000 : ℝ)|^4151 ≤ (6629371869601/50000000000000 : ℝ)^3127
        have hw : |(-2182579699/10000000000 : ℝ)|=(2182579699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395792049/10000000000 : ℝ)|^4151 ≤ (44087067193603/100000000000000 : ℝ)^3127
        have hw : |(5395792049/10000000000 : ℝ)|=(5395792049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2631573693/5000000000 : ℝ)|^4151 ≤ (8530837809721/20000000000000 : ℝ)^3127
        have hw : |(2631573693/5000000000 : ℝ)|=(2631573693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s5_1 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672705967/5000000000 : ℝ)*x 0 + (-2249899747/10000000000 : ℝ)*x 1 + (1315786839/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672705967/5000000000 : ℝ)^4151 ≤ (21770733720731/50000000000000 : ℝ)^3127 := by
    have hnat : (2672705967 : ℕ)^4151*50000000000000^3127 ≤ 21770733720731^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672705967 5000000000 21770733720731 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249899747/10000000000 : ℝ)^4151 ≤ (13804343824717/100000000000000 : ℝ)^3127 := by
    have hnat : (2249899747 : ℕ)^4151*100000000000000^3127 ≤ 13804343824717^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249899747 10000000000 13804343824717 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315786839/2500000000 : ℝ)^4151 ≤ (21327094362929/50000000000000 : ℝ)^3127 := by
    have hnat : (1315786839 : ℕ)^4151*50000000000000^3127 ≤ 21327094362929^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315786839 2500000000 21327094362929 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672705967/5000000000 : ℝ), (-2249899747/10000000000 : ℝ), (1315786839/2500000000 : ℝ)] ![(21770733720731/50000000000000 : ℝ), (13804343824717/100000000000000 : ℝ), (21327094362929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672705967/5000000000 : ℝ)|^4151 ≤ (21770733720731/50000000000000 : ℝ)^3127
        have hw : |(2672705967/5000000000 : ℝ)|=(2672705967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2249899747/10000000000 : ℝ)|^4151 ≤ (13804343824717/100000000000000 : ℝ)^3127
        have hw : |(-2249899747/10000000000 : ℝ)|=(2249899747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315786839/2500000000 : ℝ)|^4151 ≤ (21327094362929/50000000000000 : ℝ)^3127
        have hw : |(1315786839/2500000000 : ℝ)|=(1315786839/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s5_2 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345411911/10000000000 : ℝ)*x 0 + (526314739/1000000000 : ℝ)*x 1 + (-562474933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345411911/10000000000 : ℝ)^4151 ≤ (21770733596381/50000000000000 : ℝ)^3127 := by
    have hnat : (5345411911 : ℕ)^4151*50000000000000^3127 ≤ 21770733596381^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345411911 10000000000 21770733596381 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526314739/1000000000 : ℝ)^4151 ≤ (21327094545819/50000000000000 : ℝ)^3127 := by
    have hnat : (526314739 : ℕ)^4151*50000000000000^3127 ≤ 21327094545819^3127*1000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526314739 1000000000 21327094545819 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562474933/2500000000 : ℝ)^4151 ≤ (2760868740509/20000000000000 : ℝ)^3127 := by
    have hnat : (562474933 : ℕ)^4151*20000000000000^3127 ≤ 2760868740509^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562474933 2500000000 2760868740509 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345411911/10000000000 : ℝ), (526314739/1000000000 : ℝ), (-562474933/2500000000 : ℝ)] ![(21770733596381/50000000000000 : ℝ), (21327094545819/50000000000000 : ℝ), (2760868740509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345411911/10000000000 : ℝ)|^4151 ≤ (21770733596381/50000000000000 : ℝ)^3127
        have hw : |(5345411911/10000000000 : ℝ)|=(5345411911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526314739/1000000000 : ℝ)|^4151 ≤ (21327094545819/50000000000000 : ℝ)^3127
        have hw : |(526314739/1000000000 : ℝ)|=(526314739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-562474933/2500000000 : ℝ)|^4151 ≤ (2760868740509/20000000000000 : ℝ)^3127
        have hw : |(-562474933/2500000000 : ℝ)|=(562474933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s5_3 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2184616999/5000000000 : ℝ)*x 0 + (4240113033/10000000000 : ℝ)*x 1 + (4502299141/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2184616999/5000000000 : ℝ)^4151 ≤ (16657839873731/50000000000000 : ℝ)^3127 := by
    have hnat : (2184616999 : ℕ)^4151*50000000000000^3127 ≤ 16657839873731^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2184616999 5000000000 16657839873731 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240113033/10000000000 : ℝ)^4151 ≤ (32015078161197/100000000000000 : ℝ)^3127 := by
    have hnat : (4240113033 : ℕ)^4151*100000000000000^3127 ≤ 32015078161197^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240113033 10000000000 32015078161197 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4502299141/10000000000 : ℝ)^4151 ≤ (17334621035941/50000000000000 : ℝ)^3127 := by
    have hnat : (4502299141 : ℕ)^4151*50000000000000^3127 ≤ 17334621035941^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502299141 10000000000 17334621035941 50000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2184616999/5000000000 : ℝ), (4240113033/10000000000 : ℝ), (4502299141/10000000000 : ℝ)] ![(16657839873731/50000000000000 : ℝ), (32015078161197/100000000000000 : ℝ), (17334621035941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2184616999/5000000000 : ℝ)|^4151 ≤ (16657839873731/50000000000000 : ℝ)^3127
        have hw : |(2184616999/5000000000 : ℝ)|=(2184616999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240113033/10000000000 : ℝ)|^4151 ≤ (32015078161197/100000000000000 : ℝ)^3127
        have hw : |(4240113033/10000000000 : ℝ)|=(4240113033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4502299141/10000000000 : ℝ)|^4151 ≤ (17334621035941/50000000000000 : ℝ)^3127
        have hw : |(4502299141/10000000000 : ℝ)|=(4502299141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s5_4 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2182585151/10000000000 : ℝ)*x 0 + (1315872777/2500000000 : ℝ)*x 1 + (5395447057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182585151/10000000000 : ℝ)^4151 ≤ (828674231551/6250000000000 : ℝ)^3127 := by
    have hnat : (2182585151 : ℕ)^4151*6250000000000^3127 ≤ 828674231551^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182585151 10000000000 828674231551 6250000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315872777/2500000000 : ℝ)^4151 ≤ (10664471732513/25000000000000 : ℝ)^3127 := by
    have hnat : (1315872777 : ℕ)^4151*25000000000000^3127 ≤ 10664471732513^3127*2500000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315872777 2500000000 10664471732513 25000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395447057/10000000000 : ℝ)^4151 ≤ (5510415669069/12500000000000 : ℝ)^3127 := by
    have hnat : (5395447057 : ℕ)^4151*12500000000000^3127 ≤ 5510415669069^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395447057 10000000000 5510415669069 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2182585151/10000000000 : ℝ), (1315872777/2500000000 : ℝ), (5395447057/10000000000 : ℝ)] ![(828674231551/6250000000000 : ℝ), (10664471732513/25000000000000 : ℝ), (5510415669069/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2182585151/10000000000 : ℝ)|^4151 ≤ (828674231551/6250000000000 : ℝ)^3127
        have hw : |(-2182585151/10000000000 : ℝ)|=(2182585151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315872777/2500000000 : ℝ)|^4151 ≤ (10664471732513/25000000000000 : ℝ)^3127
        have hw : |(1315872777/2500000000 : ℝ)|=(1315872777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395447057/10000000000 : ℝ)|^4151 ≤ (5510415669069/12500000000000 : ℝ)^3127
        have hw : |(5395447057/10000000000 : ℝ)|=(5395447057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s5_5 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311889631/10000000000 : ℝ)*x 0 + (-264700007/1250000000 : ℝ)*x 1 + (5395447057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311889631/10000000000 : ℝ)^4151 ≤ (43179363058973/100000000000000 : ℝ)^3127 := by
    have hnat : (5311889631 : ℕ)^4151*100000000000000^3127 ≤ 43179363058973^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311889631 10000000000 43179363058973 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (264700007/1250000000 : ℝ)^4151 ≤ (1592163946269/12500000000000 : ℝ)^3127 := by
    have hnat : (264700007 : ℕ)^4151*12500000000000^3127 ≤ 1592163946269^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264700007 1250000000 1592163946269 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395447057/10000000000 : ℝ)^4151 ≤ (5510415669069/12500000000000 : ℝ)^3127 := by
    have hnat : (5395447057 : ℕ)^4151*12500000000000^3127 ≤ 5510415669069^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395447057 10000000000 5510415669069 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311889631/10000000000 : ℝ), (-264700007/1250000000 : ℝ), (5395447057/10000000000 : ℝ)] ![(43179363058973/100000000000000 : ℝ), (1592163946269/12500000000000 : ℝ), (5510415669069/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311889631/10000000000 : ℝ)|^4151 ≤ (43179363058973/100000000000000 : ℝ)^3127
        have hw : |(5311889631/10000000000 : ℝ)|=(5311889631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-264700007/1250000000 : ℝ)|^4151 ≤ (1592163946269/12500000000000 : ℝ)^3127
        have hw : |(-264700007/1250000000 : ℝ)|=(264700007/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395447057/10000000000 : ℝ)|^4151 ≤ (5510415669069/12500000000000 : ℝ)^3127
        have hw : |(5395447057/10000000000 : ℝ)|=(5395447057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s5_6 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311889633/10000000000 : ℝ)*x 0 + (5395447057/10000000000 : ℝ)*x 1 + (-1058800027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311889633/10000000000 : ℝ)^4151 ≤ (8635872616111/20000000000000 : ℝ)^3127 := by
    have hnat : (5311889633 : ℕ)^4151*20000000000000^3127 ≤ 8635872616111^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311889633 10000000000 8635872616111 20000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395447057/10000000000 : ℝ)^4151 ≤ (5510415669069/12500000000000 : ℝ)^3127 := by
    have hnat : (5395447057 : ℕ)^4151*12500000000000^3127 ≤ 5510415669069^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395447057 10000000000 5510415669069 12500000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058800027/5000000000 : ℝ)^4151 ≤ (12737311554183/100000000000000 : ℝ)^3127 := by
    have hnat : (1058800027 : ℕ)^4151*100000000000000^3127 ≤ 12737311554183^3127*5000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058800027 5000000000 12737311554183 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311889633/10000000000 : ℝ), (5395447057/10000000000 : ℝ), (-1058800027/5000000000 : ℝ)] ![(8635872616111/20000000000000 : ℝ), (5510415669069/12500000000000 : ℝ), (12737311554183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311889633/10000000000 : ℝ)|^4151 ≤ (8635872616111/20000000000000 : ℝ)^3127
        have hw : |(5311889633/10000000000 : ℝ)|=(5311889633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395447057/10000000000 : ℝ)|^4151 ≤ (5510415669069/12500000000000 : ℝ)^3127
        have hw : |(5395447057/10000000000 : ℝ)|=(5395447057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1058800027/5000000000 : ℝ)|^4151 ≤ (12737311554183/100000000000000 : ℝ)^3127
        have hw : |(-1058800027/5000000000 : ℝ)|=(1058800027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1109_s5_7 (p : ℝ) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4369244821/10000000000 : ℝ)*x 0 + (562702467/1250000000 : ℝ)*x 1 + (848158991/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4369244821/10000000000 : ℝ)^4151 ≤ (3331578929839/10000000000000 : ℝ)^3127 := by
    have hnat : (4369244821 : ℕ)^4151*10000000000000^3127 ≤ 3331578929839^3127*10000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369244821 10000000000 3331578929839 10000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562702467/1250000000 : ℝ)^4151 ≤ (34662297381947/100000000000000 : ℝ)^3127 := by
    have hnat : (562702467 : ℕ)^4151*100000000000000^3127 ≤ 34662297381947^3127*1250000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562702467 1250000000 34662297381947 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848158991/2000000000 : ℝ)^4151 ≤ (32021913312331/100000000000000 : ℝ)^3127 := by
    have hnat : (848158991 : ℕ)^4151*100000000000000^3127 ≤ 32021913312331^3127*2000000000^4151 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848158991 2000000000 32021913312331 100000000000000 4151 3127 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4151/1024 : ℝ)) 4151 3127 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4369244821/10000000000 : ℝ), (562702467/1250000000 : ℝ), (848158991/2000000000 : ℝ)] ![(3331578929839/10000000000000 : ℝ), (34662297381947/100000000000000 : ℝ), (32021913312331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4369244821/10000000000 : ℝ)|^4151 ≤ (3331578929839/10000000000000 : ℝ)^3127
        have hw : |(4369244821/10000000000 : ℝ)|=(4369244821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562702467/1250000000 : ℝ)|^4151 ≤ (34662297381947/100000000000000 : ℝ)^3127
        have hw : |(562702467/1250000000 : ℝ)|=(562702467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848158991/2000000000 : ℝ)|^4151 ≤ (32021913312331/100000000000000 : ℝ)^3127
        have hw : |(848158991/2000000000 : ℝ)|=(848158991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1109_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5633/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (563/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11111/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11111/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11111/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11111/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11111/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11111/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11111/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (1355891812195237/10000000000000000000 : ℝ) := by
    have hpowers : (11111/100000 : ℝ)^8301 ≤ (1355891812195237/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11111 : ℕ)^8301*10000000000000000000^2048 ≤ 1355891812195237^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11111 100000 1355891812195237 10000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11111/100000 : ℝ)) (X := (1355891812195237/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8301/2048 : ℝ) ≤ (37035364489902271/100000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8301 ≤ (37035364489902271/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8301*100000000000000000000^2048 ≤ 37035364489902271^2048*100000^8301 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 37035364489902271 100000000000000000000 8301 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (37035364489902271/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001355891812195237/5000000000000000000 : ℝ) ≤ (1000066897551031/1000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (5001355891812195237/5000000000000000000 : ℝ)^2048 ≤ (1000066897551031/1000000000000000 : ℝ)^8301 := by
      have hnat : (5001355891812195237 : ℕ)^2048*1000000000000000^8301 ≤ 1000066897551031^8301*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001355891812195237 5000000000000000000 1000066897551031 1000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000066897551031/1000000000000000 : ℝ)) (X := (5001355891812195237/5000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050594282611854641/100000000000000000000 : ℝ) ≤ (1000124801049821/1000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (100050594282611854641/100000000000000000000 : ℝ)^2048 ≤ (1000124801049821/1000000000000000 : ℝ)^8301 := by
      have hnat : (100050594282611854641 : ℕ)^2048*1000000000000000^8301 ≤ 1000124801049821^8301*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050594282611854641 100000000000000000000 1000124801049821 1000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000124801049821/1000000000000000 : ℝ)) (X := (100050594282611854641/100000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037035364489902271/50000000000000000000 : ℝ) ≤ (1000182704548611/1000000000000000 : ℝ) ^ (8301/2048 : ℝ) := by
    have hpowers : (50037035364489902271/50000000000000000000 : ℝ)^2048 ≤ (1000182704548611/1000000000000000 : ℝ)^8301 := by
      have hnat : (50037035364489902271 : ℕ)^2048*1000000000000000^8301 ≤ 1000182704548611^8301*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037035364489902271 50000000000000000000 1000182704548611 1000000000000000 2048 8301 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000182704548611/1000000000000000 : ℝ)) (X := (50037035364489902271/50000000000000000000 : ℝ)) (by norm_num) 8301 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1355891812195237/10000000000000000000 : ℝ) ≤ ((1562461195097205763/1563000000000000000 : ℝ)+2*(5790349879/3126000000000 : ℝ)*(11111/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (1562461195097205763/1563000000000000000 : ℝ)+2*(5790349879/3126000000000 : ℝ)*(11111/100000 : ℝ)=(1000066897551031/1000000000000000 : ℝ) by norm_num, show 1+2*(1355891812195237/10000000000000000000 : ℝ)=(5001355891812195237/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37035364489902271/100000000000000000000 : ℝ)+(1355891812195237/10000000000000000000 : ℝ) ≤ ((1562461195097205763/1563000000000000000 : ℝ)+(5790349879/3126000000000 : ℝ)*((14237/100000 : ℝ)+(11111/100000 : ℝ)))^(8301/2048 : ℝ) := by
    rw [show (1562461195097205763/1563000000000000000 : ℝ)+(5790349879/3126000000000 : ℝ)*((14237/100000 : ℝ)+(11111/100000 : ℝ))=(1000124801049821/1000000000000000 : ℝ) by norm_num, show 1+(37035364489902271/100000000000000000000 : ℝ)+(1355891812195237/10000000000000000000 : ℝ)=(100050594282611854641/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37035364489902271/100000000000000000000 : ℝ) ≤ ((1562461195097205763/1563000000000000000 : ℝ)+2*(5790349879/3126000000000 : ℝ)*(14237/100000 : ℝ))^(8301/2048 : ℝ) := by
    rw [show (1562461195097205763/1563000000000000000 : ℝ)+2*(5790349879/3126000000000 : ℝ)*(14237/100000 : ℝ)=(1000182704548611/1000000000000000 : ℝ) by norm_num, show 1+2*(37035364489902271/100000000000000000000 : ℝ)=(50037035364489902271/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1562461195097205763/1563000000000000000 : ℝ)*(X 1 0+X 2 0)+(5790349879/3126000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11111/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1562461195097205763/1563000000000000000 : ℝ)) (alpha := (5790349879/3126000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1562461195097205763/1563000000000000000 : ℝ)*(X 0 1+X 2 1)+(5790349879/3126000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11111/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1562461195097205763/1563000000000000000 : ℝ)) (alpha := (5790349879/3126000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1562461195097205763/1563000000000000000 : ℝ)*(X 0 2+X 1 2)+(5790349879/3126000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8301/2048 : ℝ)) (lo := (11111/100000 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (1562461195097205763/1563000000000000000 : ℝ)) (alpha := (5790349879/3126000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2182579699/10000000000 : ℝ)*X 0 0+(5395792049/10000000000 : ℝ)*X 0 1+(2631573693/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672705967/5000000000 : ℝ)*X 1 0+(-2249899747/10000000000 : ℝ)*X 1 1+(1315786839/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345411911/10000000000 : ℝ)*X 2 0+(526314739/1000000000 : ℝ)*X 2 1+(-562474933/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2184616999/5000000000 : ℝ)*X 0 0+(4240113033/10000000000 : ℝ)*X 0 1+(4502299141/10000000000 : ℝ)*X 0 2+(2184616999/5000000000 : ℝ)*X 1 0+(4240113033/10000000000 : ℝ)*X 1 1+(4502299141/10000000000 : ℝ)*X 1 2+(2184616999/5000000000 : ℝ)*X 2 0+(4240113033/10000000000 : ℝ)*X 2 1+(4502299141/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2182585151/10000000000 : ℝ)*X 0 0+(1315872777/2500000000 : ℝ)*X 0 1+(5395447057/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311889631/10000000000 : ℝ)*X 1 0+(-264700007/1250000000 : ℝ)*X 1 1+(5395447057/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311889633/10000000000 : ℝ)*X 2 0+(5395447057/10000000000 : ℝ)*X 2 1+(-1058800027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4369244821/10000000000 : ℝ)*X 0 0+(562702467/1250000000 : ℝ)*X 0 1+(848158991/2000000000 : ℝ)*X 0 2+(4369244821/10000000000 : ℝ)*X 1 0+(562702467/1250000000 : ℝ)*X 1 1+(848158991/2000000000 : ℝ)*X 1 2+(4369244821/10000000000 : ℝ)*X 2 0+(562702467/1250000000 : ℝ)*X 2 1+(848158991/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1109_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (66406801110078732798821329/13025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1039847197/100000000000000 : ℝ)*(base19) + (193649613/20000000000000 : ℝ)*(base23) + (10466501/50000000000000 : ℝ)*(lower2) + (56685493/50000000000000 : ℝ)*(upper3) + (6301723/6250000000000 : ℝ)*(upper5) + (5676552657111083/100000000000000 : ℝ)*(major0) + (5676552657111083/100000000000000 : ℝ)*(major1) + (5676552657111083/100000000000000 : ℝ)*(major2) + (1507793191897539/20000000000000 : ℝ)*(sp0) + (7538991871508581/100000000000000 : ℝ)*(sp1) + (7538991943107713/100000000000000 : ℝ)*(sp2) + (953524559616009/25000000000000 : ℝ)*(sp3) + (6737967021/25000000000000 : ℝ)*(sp4) + (13994455313/100000000000000 : ℝ)*(sp7) + (76282244658387/2000000000000 : ℝ)*(f.failure) + (3769496455677889/50000000000000 : ℝ)*(f.sum) + (6033937590307/781500000000000000000000000 : ℝ)*base65 + (432693320225209557/52100000000000000000000000000000 : ℝ)*base68 + (346457940293809557/52100000000000000000000000000000 : ℝ)*base70 + (780928619143590443/52100000000000000000000000000000 : ℝ)*base71 + (10720436835517/1563000000000000000000000000 : ℝ)*base74 + (946286166527609557/52100000000000000000000000000000 : ℝ)*base76 + (259266839473309557/52100000000000000000000000000000 : ℝ)*base78 + (80887285755509557/52100000000000000000000000000000 : ℝ)*base80 + (1155813098869/312600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1831589/200000000000000000000 : ℝ)*base89 + (1831589/200000000000000000000 : ℝ)*base91 + (1831589/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43180062384288761231433689/13025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (616818679/100000000000000 : ℝ)*(base19) + (677234459/100000000000000 : ℝ)*(base23) + (2712433/4000000000000 : ℝ)*(upper3) + (25721997/100000000000000 : ℝ)*(lower4) + (13784127/20000000000000 : ℝ)*(upper5) + (2853069358662803/50000000000000 : ℝ)*(major0) + (2853069358662803/50000000000000 : ℝ)*(major1) + (2853069358662803/50000000000000 : ℝ)*(major2) + (1634218361/10000000000000 : ℝ)*(sp1) + (4447587307/25000000000000 : ℝ)*(sp2) + (7578286027117387/100000000000000 : ℝ)*(sp4) + (3789134534057549/50000000000000 : ℝ)*(sp5) + (7578267559533701/100000000000000 : ℝ)*(sp6) + (1916995648514111/50000000000000 : ℝ)*(sp7) + (1916995648514111/50000000000000 : ℝ)*(f.failure) + (7578286027117387/100000000000000 : ℝ)*(f.sum) + (878703088747/312600000000000000000000000 : ℝ)*base66 + (23327325149455437/26050000000000000000000000000000 : ℝ)*base68 + (56080476150494563/26050000000000000000000000000000 : ℝ)*base69 + (175977841334055437/26050000000000000000000000000000 : ℝ)*base72 + (2543681069999/781500000000000000000000000 : ℝ)*base73 + (162654123795855437/26050000000000000000000000000000 : ℝ)*base76 + (17757939934794563/26050000000000000000000000000000 : ℝ)*base77 + (350066954659505437/26050000000000000000000000000000 : ℝ)*base80 + (93165473/4884375000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (23115417/5000000000000000000000 : ℝ)*base89 + (23115417/5000000000000000000000 : ℝ)*base91 + (23115417/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1109_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1109_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1109_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16603/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1109_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1109_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1109_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8301/2048 : ℝ) ≤ p) (hpb : p ≤ (4151/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148830247/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16603/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4459/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/4000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1109_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
