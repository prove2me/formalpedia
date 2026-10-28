-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1147_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:43.817742+00:00
-- url     : https://prove2.me/submissions/2c85d977-ead7-45f5-86dd-5bae2dd3d9f7

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
theorem support_rectangle_w1147_s0_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1890229313/10000000000 : ℝ)*x 0 + (6053175201/10000000000 : ℝ)*x 1 + (2390552187/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1890229313/10000000000 : ℝ)^2085 ≤ (686918587377/6250000000000 : ℝ)^1573 := by
    have hnat : (1890229313 : ℕ)^2085*6250000000000^1573 ≤ 686918587377^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1890229313 10000000000 686918587377 6250000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6053175201/10000000000 : ℝ)^2085 ≤ (51406777928339/100000000000000 : ℝ)^1573 := by
    have hnat : (6053175201 : ℕ)^2085*100000000000000^1573 ≤ 51406777928339^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6053175201 10000000000 51406777928339 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2390552187/5000000000 : ℝ)^2085 ≤ (37602524659071/100000000000000 : ℝ)^1573 := by
    have hnat : (2390552187 : ℕ)^2085*100000000000000^1573 ≤ 37602524659071^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390552187 5000000000 37602524659071 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1890229313/10000000000 : ℝ), (6053175201/10000000000 : ℝ), (2390552187/5000000000 : ℝ)] ![(686918587377/6250000000000 : ℝ), (51406777928339/100000000000000 : ℝ), (37602524659071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1890229313/10000000000 : ℝ)|^2085 ≤ (686918587377/6250000000000 : ℝ)^1573
        have hw : |(-1890229313/10000000000 : ℝ)|=(1890229313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6053175201/10000000000 : ℝ)|^2085 ≤ (51406777928339/100000000000000 : ℝ)^1573
        have hw : |(6053175201/10000000000 : ℝ)|=(6053175201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2390552187/5000000000 : ℝ)|^2085 ≤ (37602524659071/100000000000000 : ℝ)^1573
        have hw : |(2390552187/5000000000 : ℝ)|=(2390552187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s0_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5516511879/10000000000 : ℝ)*x 0 + (-655026583/2500000000 : ℝ)*x 1 + (2390552211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516511879/10000000000 : ℝ)^2085 ≤ (11363660978233/25000000000000 : ℝ)^1573 := by
    have hnat : (5516511879 : ℕ)^2085*25000000000000^1573 ≤ 11363660978233^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516511879 10000000000 11363660978233 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655026583/2500000000 : ℝ)^2085 ≤ (16942830912941/100000000000000 : ℝ)^1573 := by
    have hnat : (655026583 : ℕ)^2085*100000000000000^1573 ≤ 16942830912941^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655026583 2500000000 16942830912941 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2390552211/5000000000 : ℝ)^2085 ≤ (1880126257973/5000000000000 : ℝ)^1573 := by
    have hnat : (2390552211 : ℕ)^2085*5000000000000^1573 ≤ 1880126257973^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2390552211 5000000000 1880126257973 5000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516511879/10000000000 : ℝ), (-655026583/2500000000 : ℝ), (2390552211/5000000000 : ℝ)] ![(11363660978233/25000000000000 : ℝ), (16942830912941/100000000000000 : ℝ), (1880126257973/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516511879/10000000000 : ℝ)|^2085 ≤ (11363660978233/25000000000000 : ℝ)^1573
        have hw : |(5516511879/10000000000 : ℝ)|=(5516511879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-655026583/2500000000 : ℝ)|^2085 ≤ (16942830912941/100000000000000 : ℝ)^1573
        have hw : |(-655026583/2500000000 : ℝ)|=(655026583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2390552211/5000000000 : ℝ)|^2085 ≤ (1880126257973/5000000000000 : ℝ)^1573
        have hw : |(2390552211/5000000000 : ℝ)|=(2390552211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s0_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5516512179/10000000000 : ℝ)*x 0 + (1195276073/2500000000 : ℝ)*x 1 + (-655026527/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516512179/10000000000 : ℝ)^2085 ≤ (5681830898681/12500000000000 : ℝ)^1573 := by
    have hnat : (5516512179 : ℕ)^2085*12500000000000^1573 ≤ 5681830898681^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516512179 10000000000 5681830898681 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195276073/2500000000 : ℝ)^2085 ≤ (37602523804241/100000000000000 : ℝ)^1573 := by
    have hnat : (1195276073 : ℕ)^2085*100000000000000^1573 ≤ 37602523804241^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195276073 2500000000 37602523804241 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655026527/2500000000 : ℝ)^2085 ≤ (847141449649/5000000000000 : ℝ)^1573 := by
    have hnat : (655026527 : ℕ)^2085*5000000000000^1573 ≤ 847141449649^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655026527 2500000000 847141449649 5000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516512179/10000000000 : ℝ), (1195276073/2500000000 : ℝ), (-655026527/2500000000 : ℝ)] ![(5681830898681/12500000000000 : ℝ), (37602523804241/100000000000000 : ℝ), (847141449649/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516512179/10000000000 : ℝ)|^2085 ≤ (5681830898681/12500000000000 : ℝ)^1573
        have hw : |(5516512179/10000000000 : ℝ)|=(5516512179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195276073/2500000000 : ℝ)|^2085 ≤ (37602523804241/100000000000000 : ℝ)^1573
        have hw : |(1195276073/2500000000 : ℝ)|=(1195276073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-655026527/2500000000 : ℝ)|^2085 ≤ (847141449649/5000000000000 : ℝ)^1573
        have hw : |(-655026527/2500000000 : ℝ)|=(655026527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s0_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4200586787/10000000000 : ℝ)*x 0 + (3120847969/10000000000 : ℝ)*x 1 + (2827041167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200586787/10000000000 : ℝ)^2085 ≤ (15836897754079/50000000000000 : ℝ)^1573 := by
    have hnat : (4200586787 : ℕ)^2085*50000000000000^1573 ≤ 15836897754079^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200586787 10000000000 15836897754079 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3120847969/10000000000 : ℝ)^2085 ≤ (2670373800527/12500000000000 : ℝ)^1573 := by
    have hnat : (3120847969 : ℕ)^2085*12500000000000^1573 ≤ 2670373800527^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3120847969 10000000000 2670373800527 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2827041167/5000000000 : ℝ)^2085 ≤ (4696321407479/10000000000000 : ℝ)^1573 := by
    have hnat : (2827041167 : ℕ)^2085*10000000000000^1573 ≤ 4696321407479^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2827041167 5000000000 4696321407479 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200586787/10000000000 : ℝ), (3120847969/10000000000 : ℝ), (2827041167/5000000000 : ℝ)] ![(15836897754079/50000000000000 : ℝ), (2670373800527/12500000000000 : ℝ), (4696321407479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200586787/10000000000 : ℝ)|^2085 ≤ (15836897754079/50000000000000 : ℝ)^1573
        have hw : |(4200586787/10000000000 : ℝ)|=(4200586787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3120847969/10000000000 : ℝ)|^2085 ≤ (2670373800527/12500000000000 : ℝ)^1573
        have hw : |(3120847969/10000000000 : ℝ)|=(3120847969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2827041167/5000000000 : ℝ)|^2085 ≤ (4696321407479/10000000000000 : ℝ)^1573
        have hw : |(2827041167/5000000000 : ℝ)|=(2827041167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s0_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-947680071/5000000000 : ℝ)*x 0 + (1203479431/2500000000 : ℝ)*x 1 + (6019207831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (947680071/5000000000 : ℝ)^2085 ≤ (5515129202081/50000000000000 : ℝ)^1573 := by
    have hnat : (947680071 : ℕ)^2085*50000000000000^1573 ≤ 5515129202081^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947680071 5000000000 5515129202081 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1203479431/2500000000 : ℝ)^2085 ≤ (18972488743321/50000000000000 : ℝ)^1573 := by
    have hnat : (1203479431 : ℕ)^2085*50000000000000^1573 ≤ 18972488743321^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1203479431 2500000000 18972488743321 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6019207831/10000000000 : ℝ)^2085 ≤ (25512382044911/50000000000000 : ℝ)^1573 := by
    have hnat : (6019207831 : ℕ)^2085*50000000000000^1573 ≤ 25512382044911^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019207831 10000000000 25512382044911 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-947680071/5000000000 : ℝ), (1203479431/2500000000 : ℝ), (6019207831/10000000000 : ℝ)] ![(5515129202081/50000000000000 : ℝ), (18972488743321/50000000000000 : ℝ), (25512382044911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-947680071/5000000000 : ℝ)|^2085 ≤ (5515129202081/50000000000000 : ℝ)^1573
        have hw : |(-947680071/5000000000 : ℝ)|=(947680071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1203479431/2500000000 : ℝ)|^2085 ≤ (18972488743321/50000000000000 : ℝ)^1573
        have hw : |(1203479431/2500000000 : ℝ)|=(1203479431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6019207831/10000000000 : ℝ)|^2085 ≤ (25512382044911/50000000000000 : ℝ)^1573
        have hw : |(6019207831/10000000000 : ℝ)|=(6019207831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s0_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (517083733/1000000000 : ℝ)*x 0 + (-1382002909/10000000000 : ℝ)*x 1 + (2351253/3906250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517083733/1000000000 : ℝ)^2085 ≤ (1668733658827/4000000000000 : ℝ)^1573 := by
    have hnat : (517083733 : ℕ)^2085*4000000000000^1573 ≤ 1668733658827^1573*1000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517083733 1000000000 1668733658827 4000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382002909/10000000000 : ℝ)^2085 ≤ (1451379224129/20000000000000 : ℝ)^1573 := by
    have hnat : (1382002909 : ℕ)^2085*20000000000000^1573 ≤ 1451379224129^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382002909 10000000000 1451379224129 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2351253/3906250 : ℝ)^2085 ≤ (25512381196579/50000000000000 : ℝ)^1573 := by
    have hnat : (2351253 : ℕ)^2085*50000000000000^1573 ≤ 25512381196579^1573*3906250^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2351253 3906250 25512381196579 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517083733/1000000000 : ℝ), (-1382002909/10000000000 : ℝ), (2351253/3906250 : ℝ)] ![(1668733658827/4000000000000 : ℝ), (1451379224129/20000000000000 : ℝ), (25512381196579/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517083733/1000000000 : ℝ)|^2085 ≤ (1668733658827/4000000000000 : ℝ)^1573
        have hw : |(517083733/1000000000 : ℝ)|=(517083733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1382002909/10000000000 : ℝ)|^2085 ≤ (1451379224129/20000000000000 : ℝ)^1573
        have hw : |(-1382002909/10000000000 : ℝ)|=(1382002909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2351253/3906250 : ℝ)|^2085 ≤ (25512381196579/50000000000000 : ℝ)^1573
        have hw : |(2351253/3906250 : ℝ)|=(2351253/3906250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s0_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2585418663/5000000000 : ℝ)*x 0 + (6019207717/10000000000 : ℝ)*x 1 + (-172750357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2585418663/5000000000 : ℝ)^2085 ≤ (20859170713949/50000000000000 : ℝ)^1573 := by
    have hnat : (2585418663 : ℕ)^2085*50000000000000^1573 ≤ 20859170713949^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585418663 5000000000 20859170713949 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6019207717/10000000000 : ℝ)^2085 ≤ (51024762808897/100000000000000 : ℝ)^1573 := by
    have hnat : (6019207717 : ℕ)^2085*100000000000000^1573 ≤ 51024762808897^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019207717 10000000000 51024762808897 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (172750357/1250000000 : ℝ)^2085 ≤ (7256895751757/100000000000000 : ℝ)^1573 := by
    have hnat : (172750357 : ℕ)^2085*100000000000000^1573 ≤ 7256895751757^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172750357 1250000000 7256895751757 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2585418663/5000000000 : ℝ), (6019207717/10000000000 : ℝ), (-172750357/1250000000 : ℝ)] ![(20859170713949/50000000000000 : ℝ), (51024762808897/100000000000000 : ℝ), (7256895751757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2585418663/5000000000 : ℝ)|^2085 ≤ (20859170713949/50000000000000 : ℝ)^1573
        have hw : |(2585418663/5000000000 : ℝ)|=(2585418663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6019207717/10000000000 : ℝ)|^2085 ≤ (51024762808897/100000000000000 : ℝ)^1573
        have hw : |(6019207717/10000000000 : ℝ)|=(6019207717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-172750357/1250000000 : ℝ)|^2085 ≤ (7256895751757/100000000000000 : ℝ)^1573
        have hw : |(-172750357/1250000000 : ℝ)|=(172750357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s0_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42108047/100000000 : ℝ)*x 0 + (2794368393/5000000000 : ℝ)*x 1 + (6227523/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42108047/100000000 : ℝ)^2085 ≤ (31775960354079/100000000000000 : ℝ)^1573 := by
    have hnat : (42108047 : ℕ)^2085*100000000000000^1573 ≤ 31775960354079^1573*100000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42108047 100000000 31775960354079 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794368393/5000000000 : ℝ)^2085 ≤ (4624513998769/10000000000000 : ℝ)^1573 := by
    have hnat : (2794368393 : ℕ)^2085*10000000000000^1573 ≤ 4624513998769^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794368393 5000000000 4624513998769 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6227523/19531250 : ℝ)^2085 ≤ (10989449819069/50000000000000 : ℝ)^1573 := by
    have hnat : (6227523 : ℕ)^2085*50000000000000^1573 ≤ 10989449819069^1573*19531250^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6227523 19531250 10989449819069 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42108047/100000000 : ℝ), (2794368393/5000000000 : ℝ), (6227523/19531250 : ℝ)] ![(31775960354079/100000000000000 : ℝ), (4624513998769/10000000000000 : ℝ), (10989449819069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42108047/100000000 : ℝ)|^2085 ≤ (31775960354079/100000000000000 : ℝ)^1573
        have hw : |(42108047/100000000 : ℝ)|=(42108047/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794368393/5000000000 : ℝ)|^2085 ≤ (4624513998769/10000000000000 : ℝ)^1573
        have hw : |(2794368393/5000000000 : ℝ)|=(2794368393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6227523/19531250 : ℝ)|^2085 ≤ (10989449819069/50000000000000 : ℝ)^1573
        have hw : |(6227523/19531250 : ℝ)|=(6227523/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (217/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6949/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8339/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8339 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8339*1^2048 ≤ 0^2048*1^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8339/2048 : ℝ) ≤ (47940977420394303/2000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8339 ≤ (47940977420394303/2000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8339*2000000000000000000^2048 ≤ 47940977420394303^2048*5^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 47940977420394303 2000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (47940977420394303/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8339 := by
      have hnat : (1 : ℕ)^2048*1^8339 ≤ 1^8339*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2047940977420394303/2000000000000000000 : ℝ) ≤ (10058344895642801/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (2047940977420394303/2000000000000000000 : ℝ)^2048 ≤ (10058344895642801/10000000000000000 : ℝ)^8339 := by
      have hnat : (2047940977420394303 : ℕ)^2048*10000000000000000^8339 ≤ 10058344895642801^8339*2000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2047940977420394303 2000000000000000000 10058344895642801 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10058344895642801/10000000000000000 : ℝ)) (X := (2047940977420394303/2000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (1047940977420394303/1000000000000000000 : ℝ) ≤ (5058344895642801/5000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (1047940977420394303/1000000000000000000 : ℝ)^2048 ≤ (5058344895642801/5000000000000000 : ℝ)^8339 := by
      have hnat : (1047940977420394303 : ℕ)^2048*5000000000000000^8339 ≤ 5058344895642801^8339*1000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1047940977420394303 1000000000000000000 5058344895642801 5000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058344895642801/5000000000000000 : ℝ)) (X := (1047940977420394303/1000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(58344895642801/4000000000000000 : ℝ)*(0 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58344895642801/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47940977420394303/2000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(58344895642801/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (1 : ℝ)+(58344895642801/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10058344895642801/10000000000000000 : ℝ) by norm_num, show 1+(47940977420394303/2000000000000000000 : ℝ)+(0 : ℝ)=(2047940977420394303/2000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47940977420394303/2000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(58344895642801/4000000000000000 : ℝ)*(2/5 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(58344895642801/4000000000000000 : ℝ)*(2/5 : ℝ)=(5058344895642801/5000000000000000 : ℝ) by norm_num, show 1+2*(47940977420394303/2000000000000000000 : ℝ)=(1047940977420394303/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(58344895642801/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58344895642801/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(58344895642801/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58344895642801/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(58344895642801/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (58344895642801/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1890229313/10000000000 : ℝ)*X 0 0+(6053175201/10000000000 : ℝ)*X 0 1+(2390552187/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516511879/10000000000 : ℝ)*X 1 0+(-655026583/2500000000 : ℝ)*X 1 1+(2390552211/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5516512179/10000000000 : ℝ)*X 2 0+(1195276073/2500000000 : ℝ)*X 2 1+(-655026527/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4200586787/10000000000 : ℝ)*X 0 0+(3120847969/10000000000 : ℝ)*X 0 1+(2827041167/5000000000 : ℝ)*X 0 2+(4200586787/10000000000 : ℝ)*X 1 0+(3120847969/10000000000 : ℝ)*X 1 1+(2827041167/5000000000 : ℝ)*X 1 2+(4200586787/10000000000 : ℝ)*X 2 0+(3120847969/10000000000 : ℝ)*X 2 1+(2827041167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-947680071/5000000000 : ℝ)*X 0 0+(1203479431/2500000000 : ℝ)*X 0 1+(6019207831/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((517083733/1000000000 : ℝ)*X 1 0+(-1382002909/10000000000 : ℝ)*X 1 1+(2351253/3906250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2585418663/5000000000 : ℝ)*X 2 0+(6019207717/10000000000 : ℝ)*X 2 1+(-172750357/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((42108047/100000000 : ℝ)*X 0 0+(2794368393/5000000000 : ℝ)*X 0 1+(6227523/19531250 : ℝ)*X 0 2+(42108047/100000000 : ℝ)*X 1 0+(2794368393/5000000000 : ℝ)*X 1 1+(6227523/19531250 : ℝ)*X 1 2+(42108047/100000000 : ℝ)*X 2 0+(2794368393/5000000000 : ℝ)*X 2 1+(6227523/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2416366102888169187/500000000000000000000000 : ℝ) := by norm_num
    linear_combination (24102921/50000000000000 : ℝ)*(base1) + (1205300457/100000000000000 : ℝ)*(base19) + (571585471/50000000000000 : ℝ)*(base23) + (1311009/1250000000000 : ℝ)*(base24) + (140715989/50000000000000 : ℝ)*(upper3) + (590441092569727/100000000000000 : ℝ)*(major0) + (590441092569727/100000000000000 : ℝ)*(major1) + (590441092569727/100000000000000 : ℝ)*(major2) + (786123745205893/100000000000000 : ℝ)*(sp0) + (786125143557423/100000000000000 : ℝ)*(sp1) + (393062550403109/50000000000000 : ℝ)*(sp2) + (394753483736219/100000000000000 : ℝ)*(sp3) + (2651857829/100000000000000 : ℝ)*(sp4) + (428649687/20000000000000 : ℝ)*(sp7) + (12336114849703/3125000000000 : ℝ)*(f.failure) + (19653158721447/2500000000000 : ℝ)*(f.sum) + (30099347114673/200000000000000000000000000000 : ℝ)*base66 + (1919842654085327/400000000000000000000000000000 : ℝ)*base67 + (2664914343285327/400000000000000000000000000000 : ℝ)*base69 + (2691334310085327/400000000000000000000000000000 : ℝ)*base71 + (35544758914673/200000000000000000000000000000 : ℝ)*base74 + (1725758493285327/400000000000000000000000000000 : ℝ)*base75 + (2684213828085327/400000000000000000000000000000 : ℝ)*base77 + (782975867285327/400000000000000000000000000000 : ℝ)*base79 + (589270654314673/200000000000000000000000000000 : ℝ)*base82 + (321689/156250000000000000000 : ℝ)*base90 + (321689/156250000000000000000 : ℝ)*base92 + (321689/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72640470000215841503199/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73828449/100000000000000 : ℝ)*(base1) + (1434993421/100000000000000 : ℝ)*(base19) + (1433791101/100000000000000 : ℝ)*(base23) + (154750657/100000000000000 : ℝ)*(upper3) + (169582481/100000000000000 : ℝ)*(upper5) + (77893759584667/12500000000000 : ℝ)*(major0) + (77893759584667/12500000000000 : ℝ)*(major1) + (77893759584667/12500000000000 : ℝ)*(major2) + (90744511/3125000000000 : ℝ)*(sp1) + (2895437317/100000000000000 : ℝ)*(sp2) + (165935172987019/20000000000000 : ℝ)*(sp4) + (103708931536109/12500000000000 : ℝ)*(sp5) + (207417865469557/25000000000000 : ℝ)*(sp6) + (416624094711651/100000000000000 : ℝ)*(sp7) + (416624168540101/100000000000000 : ℝ)*(f.failure) + (165935158221329/20000000000000 : ℝ)*(f.sum) + (58890343282267/25000000000000000000000000000 : ℝ)*base65 + (70551124767733/50000000000000000000000000000 : ℝ)*base68 + (204499192482267/50000000000000000000000000000 : ℝ)*base69 + (286568305132267/50000000000000000000000000000 : ℝ)*base71 + (36299455817733/25000000000000000000000000000 : ℝ)*base74 + (212064564532267/50000000000000000000000000000 : ℝ)*base75 + (58965659982267/50000000000000000000000000000 : ℝ)*base77 + (114922437767733/50000000000000000000000000000 : ℝ)*base80 + (114233979232267/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (13329337/5000000000000000000000 : ℝ)*base89 + (13329337/5000000000000000000000 : ℝ)*base91 + (13329337/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1147_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (217/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6949/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1147_s1_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-65454101/312500000 : ℝ)*x 0 + (2850087951/5000000000 : ℝ)*x 1 + (312706987/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65454101/312500000 : ℝ)^2085 ≤ (12592314754309/100000000000000 : ℝ)^1573 := by
    have hnat : (65454101 : ℕ)^2085*100000000000000^1573 ≤ 12592314754309^1573*312500000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65454101 312500000 12592314754309 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2850087951/5000000000 : ℝ)^2085 ≤ (118678399027/250000000000 : ℝ)^1573 := by
    have hnat : (2850087951 : ℕ)^2085*250000000000^1573 ≤ 118678399027^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850087951 5000000000 118678399027 250000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312706987/625000000 : ℝ)^2085 ≤ (39936325619681/100000000000000 : ℝ)^1573 := by
    have hnat : (312706987 : ℕ)^2085*100000000000000^1573 ≤ 39936325619681^1573*625000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312706987 625000000 39936325619681 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65454101/312500000 : ℝ), (2850087951/5000000000 : ℝ), (312706987/625000000 : ℝ)] ![(12592314754309/100000000000000 : ℝ), (118678399027/250000000000 : ℝ), (39936325619681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65454101/312500000 : ℝ)|^2085 ≤ (12592314754309/100000000000000 : ℝ)^1573
        have hw : |(-65454101/312500000 : ℝ)|=(65454101/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2850087951/5000000000 : ℝ)|^2085 ≤ (118678399027/250000000000 : ℝ)^1573
        have hw : |(2850087951/5000000000 : ℝ)|=(2850087951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(312706987/625000000 : ℝ)|^2085 ≤ (39936325619681/100000000000000 : ℝ)^1573
        have hw : |(312706987/625000000 : ℝ)|=(312706987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s1_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1354712107/2500000000 : ℝ)*x 0 + (-1235250961/5000000000 : ℝ)*x 1 + (2501655503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1354712107/2500000000 : ℝ)^2085 ≤ (22195538324103/50000000000000 : ℝ)^1573 := by
    have hnat : (1354712107 : ℕ)^2085*50000000000000^1573 ≤ 22195538324103^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354712107 2500000000 22195538324103 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1235250961/5000000000 : ℝ)^2085 ≤ (3134521206289/20000000000000 : ℝ)^1573 := by
    have hnat : (1235250961 : ℕ)^2085*20000000000000^1573 ≤ 3134521206289^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235250961 5000000000 3134521206289 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2501655503/5000000000 : ℝ)^2085 ≤ (39936317303759/100000000000000 : ℝ)^1573 := by
    have hnat : (2501655503 : ℕ)^2085*100000000000000^1573 ≤ 39936317303759^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501655503 5000000000 39936317303759 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1354712107/2500000000 : ℝ), (-1235250961/5000000000 : ℝ), (2501655503/5000000000 : ℝ)] ![(22195538324103/50000000000000 : ℝ), (3134521206289/20000000000000 : ℝ), (39936317303759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1354712107/2500000000 : ℝ)|^2085 ≤ (22195538324103/50000000000000 : ℝ)^1573
        have hw : |(1354712107/2500000000 : ℝ)|=(1354712107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1235250961/5000000000 : ℝ)|^2085 ≤ (3134521206289/20000000000000 : ℝ)^1573
        have hw : |(-1235250961/5000000000 : ℝ)|=(1235250961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2501655503/5000000000 : ℝ)|^2085 ≤ (39936317303759/100000000000000 : ℝ)^1573
        have hw : |(2501655503/5000000000 : ℝ)|=(2501655503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s1_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2709425217/5000000000 : ℝ)*x 0 + (5003309221/10000000000 : ℝ)*x 1 + (-1235250789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709425217/5000000000 : ℝ)^2085 ≤ (44391098430167/100000000000000 : ℝ)^1573 := by
    have hnat : (2709425217 : ℕ)^2085*100000000000000^1573 ≤ 44391098430167^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709425217 5000000000 44391098430167 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5003309221/10000000000 : ℝ)^2085 ≤ (7987259683673/20000000000000 : ℝ)^1573 := by
    have hnat : (5003309221 : ℕ)^2085*20000000000000^1573 ≤ 7987259683673^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5003309221 10000000000 7987259683673 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1235250789/5000000000 : ℝ)^2085 ≤ (7836301569411/50000000000000 : ℝ)^1573 := by
    have hnat : (1235250789 : ℕ)^2085*50000000000000^1573 ≤ 7836301569411^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1235250789 5000000000 7836301569411 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709425217/5000000000 : ℝ), (5003309221/10000000000 : ℝ), (-1235250789/5000000000 : ℝ)] ![(44391098430167/100000000000000 : ℝ), (7987259683673/20000000000000 : ℝ), (7836301569411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709425217/5000000000 : ℝ)|^2085 ≤ (44391098430167/100000000000000 : ℝ)^1573
        have hw : |(2709425217/5000000000 : ℝ)|=(2709425217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5003309221/10000000000 : ℝ)|^2085 ≤ (7987259683673/20000000000000 : ℝ)^1573
        have hw : |(5003309221/10000000000 : ℝ)|=(5003309221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1235250789/5000000000 : ℝ)|^2085 ≤ (7836301569411/50000000000000 : ℝ)^1573
        have hw : |(-1235250789/5000000000 : ℝ)|=(1235250789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s1_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4317014607/10000000000 : ℝ)*x 0 + (73559477/200000000 : ℝ)*x 1 + (2532861853/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317014607/10000000000 : ℝ)^2085 ≤ (16421333632323/50000000000000 : ℝ)^1573 := by
    have hnat : (4317014607 : ℕ)^2085*50000000000000^1573 ≤ 16421333632323^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317014607 10000000000 16421333632323 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73559477/200000000 : ℝ)^2085 ≤ (6639837227329/25000000000000 : ℝ)^1573 := by
    have hnat : (73559477 : ℕ)^2085*25000000000000^1573 ≤ 6639837227329^1573*200000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73559477 200000000 6639837227329 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2532861853/5000000000 : ℝ)^2085 ≤ (20298991906851/50000000000000 : ℝ)^1573 := by
    have hnat : (2532861853 : ℕ)^2085*50000000000000^1573 ≤ 20298991906851^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532861853 5000000000 20298991906851 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317014607/10000000000 : ℝ), (73559477/200000000 : ℝ), (2532861853/5000000000 : ℝ)] ![(16421333632323/50000000000000 : ℝ), (6639837227329/25000000000000 : ℝ), (20298991906851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317014607/10000000000 : ℝ)|^2085 ≤ (16421333632323/50000000000000 : ℝ)^1573
        have hw : |(4317014607/10000000000 : ℝ)|=(4317014607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(73559477/200000000 : ℝ)|^2085 ≤ (6639837227329/25000000000000 : ℝ)^1573
        have hw : |(73559477/200000000 : ℝ)|=(73559477/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2532861853/5000000000 : ℝ)|^2085 ≤ (20298991906851/50000000000000 : ℝ)^1573
        have hw : |(2532861853/5000000000 : ℝ)|=(2532861853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s1_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095330931/10000000000 : ℝ)*x 0 + (5012808397/10000000000 : ℝ)*x 1 + (177827847/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095330931/10000000000 : ℝ)^2085 ≤ (3149671959429/25000000000000 : ℝ)^1573 := by
    have hnat : (2095330931 : ℕ)^2085*25000000000000^1573 ≤ 3149671959429^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095330931 10000000000 3149671959429 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5012808397/10000000000 : ℝ)^2085 ≤ (8007366246919/20000000000000 : ℝ)^1573 := by
    have hnat : (5012808397 : ℕ)^2085*20000000000000^1573 ≤ 8007366246919^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5012808397 10000000000 8007366246919 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177827847/312500000 : ℝ)^2085 ≤ (47364480909961/100000000000000 : ℝ)^1573 := by
    have hnat : (177827847 : ℕ)^2085*100000000000000^1573 ≤ 47364480909961^1573*312500000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177827847 312500000 47364480909961 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095330931/10000000000 : ℝ), (5012808397/10000000000 : ℝ), (177827847/312500000 : ℝ)] ![(3149671959429/25000000000000 : ℝ), (8007366246919/20000000000000 : ℝ), (47364480909961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095330931/10000000000 : ℝ)|^2085 ≤ (3149671959429/25000000000000 : ℝ)^1573
        have hw : |(-2095330931/10000000000 : ℝ)|=(2095330931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5012808397/10000000000 : ℝ)|^2085 ≤ (8007366246919/20000000000000 : ℝ)^1573
        have hw : |(5012808397/10000000000 : ℝ)|=(5012808397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(177827847/312500000 : ℝ)|^2085 ≤ (47364480909961/100000000000000 : ℝ)^1573
        have hw : |(177827847/312500000 : ℝ)|=(177827847/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s1_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5240140359/10000000000 : ℝ)*x 0 + (-1783321673/10000000000 : ℝ)*x 1 + (5690490717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5240140359/10000000000 : ℝ)^2085 ≤ (42461085461407/100000000000000 : ℝ)^1573 := by
    have hnat : (5240140359 : ℕ)^2085*100000000000000^1573 ≤ 42461085461407^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240140359 10000000000 42461085461407 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1783321673/10000000000 : ℝ)^2085 ≤ (10174437894191/100000000000000 : ℝ)^1573 := by
    have hnat : (1783321673 : ℕ)^2085*100000000000000^1573 ≤ 10174437894191^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1783321673 10000000000 10174437894191 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5690490717/10000000000 : ℝ)^2085 ≤ (47364476640321/100000000000000 : ℝ)^1573 := by
    have hnat : (5690490717 : ℕ)^2085*100000000000000^1573 ≤ 47364476640321^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690490717 10000000000 47364476640321 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5240140359/10000000000 : ℝ), (-1783321673/10000000000 : ℝ), (5690490717/10000000000 : ℝ)] ![(42461085461407/100000000000000 : ℝ), (10174437894191/100000000000000 : ℝ), (47364476640321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5240140359/10000000000 : ℝ)|^2085 ≤ (42461085461407/100000000000000 : ℝ)^1573
        have hw : |(5240140359/10000000000 : ℝ)|=(5240140359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1783321673/10000000000 : ℝ)|^2085 ≤ (10174437894191/100000000000000 : ℝ)^1573
        have hw : |(-1783321673/10000000000 : ℝ)|=(1783321673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5690490717/10000000000 : ℝ)|^2085 ≤ (47364476640321/100000000000000 : ℝ)^1573
        have hw : |(5690490717/10000000000 : ℝ)|=(5690490717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s1_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1048028087/2000000000 : ℝ)*x 0 + (5690490929/10000000000 : ℝ)*x 1 + (-891660627/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048028087/2000000000 : ℝ)^2085 ≤ (42461086277687/100000000000000 : ℝ)^1573 := by
    have hnat : (1048028087 : ℕ)^2085*100000000000000^1573 ≤ 42461086277687^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048028087 2000000000 42461086277687 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5690490929/10000000000 : ℝ)^2085 ≤ (9472895795849/20000000000000 : ℝ)^1573 := by
    have hnat : (5690490929 : ℕ)^2085*20000000000000^1573 ≤ 9472895795849^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5690490929 10000000000 9472895795849 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891660627/5000000000 : ℝ)^2085 ≤ (10174434725557/100000000000000 : ℝ)^1573 := by
    have hnat : (891660627 : ℕ)^2085*100000000000000^1573 ≤ 10174434725557^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891660627 5000000000 10174434725557 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048028087/2000000000 : ℝ), (5690490929/10000000000 : ℝ), (-891660627/5000000000 : ℝ)] ![(42461086277687/100000000000000 : ℝ), (9472895795849/20000000000000 : ℝ), (10174434725557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048028087/2000000000 : ℝ)|^2085 ≤ (42461086277687/100000000000000 : ℝ)^1573
        have hw : |(1048028087/2000000000 : ℝ)|=(1048028087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5690490929/10000000000 : ℝ)|^2085 ≤ (9472895795849/20000000000000 : ℝ)^1573
        have hw : |(5690490929/10000000000 : ℝ)|=(5690490929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-891660627/5000000000 : ℝ)|^2085 ≤ (10174434725557/100000000000000 : ℝ)^1573
        have hw : |(-891660627/5000000000 : ℝ)|=(891660627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s1_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (16869541/39062500 : ℝ)*x 0 + (504681327/1000000000 : ℝ)*x 1 + (147890357/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16869541/39062500 : ℝ)^2085 ≤ (32858680473711/100000000000000 : ℝ)^1573 := by
    have hnat : (16869541 : ℕ)^2085*100000000000000^1573 ≤ 32858680473711^1573*39062500^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16869541 39062500 32858680473711 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (504681327/1000000000 : ℝ)^2085 ≤ (40397223578981/100000000000000 : ℝ)^1573 := by
    have hnat : (504681327 : ℕ)^2085*100000000000000^1573 ≤ 40397223578981^1573*1000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      504681327 1000000000 40397223578981 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (147890357/400000000 : ℝ)^2085 ≤ (13372047969541/50000000000000 : ℝ)^1573 := by
    have hnat : (147890357 : ℕ)^2085*50000000000000^1573 ≤ 13372047969541^1573*400000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      147890357 400000000 13372047969541 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16869541/39062500 : ℝ), (504681327/1000000000 : ℝ), (147890357/400000000 : ℝ)] ![(32858680473711/100000000000000 : ℝ), (40397223578981/100000000000000 : ℝ), (13372047969541/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16869541/39062500 : ℝ)|^2085 ≤ (32858680473711/100000000000000 : ℝ)^1573
        have hw : |(16869541/39062500 : ℝ)|=(16869541/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(504681327/1000000000 : ℝ)|^2085 ≤ (40397223578981/100000000000000 : ℝ)^1573
        have hw : |(504681327/1000000000 : ℝ)|=(504681327/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(147890357/400000000 : ℝ)|^2085 ≤ (13372047969541/50000000000000 : ℝ)^1573
        have hw : |(147890357/400000000 : ℝ)|=(147890357/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6949/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (217/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5677/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4083/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6949/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (217/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6949/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (217/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6949/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (217/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6949/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (217/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6949/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (217/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6949/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (217/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (217/50000 : ℝ) ^ (8339/2048 : ℝ) ≤ (12004780139/50000000000000000000 : ℝ) := by
    have hpowers : (217/50000 : ℝ)^8339 ≤ (12004780139/50000000000000000000 : ℝ)^2048 := by
      have hnat : (217 : ℕ)^8339*50000000000000000000^2048 ≤ 12004780139^2048*50000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        217 50000 12004780139 50000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (217/50000 : ℝ)) (X := (12004780139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (6949/25000 : ℝ) ^ (8339/2048 : ℝ) ≤ (108905480204393581/20000000000000000000 : ℝ) := by
    have hpowers : (6949/25000 : ℝ)^8339 ≤ (108905480204393581/20000000000000000000 : ℝ)^2048 := by
      have hnat : (6949 : ℕ)^8339*20000000000000000000^2048 ≤ 108905480204393581^2048*25000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6949 25000 108905480204393581 20000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6949/25000 : ℝ)) (X := (108905480204393581/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000012004780139/25000000000000000000 : ℝ) ≤ (2500000000294829/2500000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (25000000012004780139/25000000000000000000 : ℝ)^2048 ≤ (2500000000294829/2500000000000000 : ℝ)^8339 := by
      have hnat : (25000000012004780139 : ℕ)^2048*2500000000000000^8339 ≤ 2500000000294829^8339*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000012004780139 25000000000000000000 2500000000294829 2500000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000000294829/2500000000000000 : ℝ)) (X := (25000000012004780139/25000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100544527425031528183/100000000000000000000 : ℝ) ≤ (2002669166218601/2000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (100544527425031528183/100000000000000000000 : ℝ)^2048 ≤ (2002669166218601/2000000000000000 : ℝ)^8339 := by
      have hnat : (100544527425031528183 : ℕ)^2048*2000000000000000^8339 ≤ 2002669166218601^8339*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100544527425031528183 100000000000000000000 2002669166218601 2000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2002669166218601/2000000000000000 : ℝ)) (X := (100544527425031528183/100000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10108905480204393581/10000000000000000000 : ℝ) ≤ (5013345830503347/5000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (10108905480204393581/10000000000000000000 : ℝ)^2048 ≤ (5013345830503347/5000000000000000 : ℝ)^8339 := by
      have hnat : (10108905480204393581 : ℕ)^2048*5000000000000000^8339 ≤ 5013345830503347^8339*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10108905480204393581 10000000000000000000 5013345830503347 5000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013345830503347/5000000000000000 : ℝ)) (X := (10108905480204393581/10000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12004780139/50000000000000000000 : ℝ) ≤ ((13680420792595168117/13681000000000000000 : ℝ)+2*(13345829913689/2736200000000000 : ℝ)*(217/50000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (13680420792595168117/13681000000000000000 : ℝ)+2*(13345829913689/2736200000000000 : ℝ)*(217/50000 : ℝ)=(2500000000294829/2500000000000000 : ℝ) by norm_num, show 1+2*(12004780139/50000000000000000000 : ℝ)=(25000000012004780139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(108905480204393581/20000000000000000000 : ℝ)+(12004780139/50000000000000000000 : ℝ) ≤ ((13680420792595168117/13681000000000000000 : ℝ)+(13345829913689/2736200000000000 : ℝ)*((6949/25000 : ℝ)+(217/50000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (13680420792595168117/13681000000000000000 : ℝ)+(13345829913689/2736200000000000 : ℝ)*((6949/25000 : ℝ)+(217/50000 : ℝ))=(2002669166218601/2000000000000000 : ℝ) by norm_num, show 1+(108905480204393581/20000000000000000000 : ℝ)+(12004780139/50000000000000000000 : ℝ)=(100544527425031528183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(108905480204393581/20000000000000000000 : ℝ) ≤ ((13680420792595168117/13681000000000000000 : ℝ)+2*(13345829913689/2736200000000000 : ℝ)*(6949/25000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (13680420792595168117/13681000000000000000 : ℝ)+2*(13345829913689/2736200000000000 : ℝ)*(6949/25000 : ℝ)=(5013345830503347/5000000000000000 : ℝ) by norm_num, show 1+2*(108905480204393581/20000000000000000000 : ℝ)=(10108905480204393581/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13680420792595168117/13681000000000000000 : ℝ)*(X 1 0+X 2 0)+(13345829913689/2736200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (217/50000 : ℝ)) (hi := (6949/25000 : ℝ)) (c := (13680420792595168117/13681000000000000000 : ℝ)) (alpha := (13345829913689/2736200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13680420792595168117/13681000000000000000 : ℝ)*(X 0 1+X 2 1)+(13345829913689/2736200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (217/50000 : ℝ)) (hi := (6949/25000 : ℝ)) (c := (13680420792595168117/13681000000000000000 : ℝ)) (alpha := (13345829913689/2736200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13680420792595168117/13681000000000000000 : ℝ)*(X 0 2+X 1 2)+(13345829913689/2736200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (217/50000 : ℝ)) (hi := (6949/25000 : ℝ)) (c := (13680420792595168117/13681000000000000000 : ℝ)) (alpha := (13345829913689/2736200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-65454101/312500000 : ℝ)*X 0 0+(2850087951/5000000000 : ℝ)*X 0 1+(312706987/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1354712107/2500000000 : ℝ)*X 1 0+(-1235250961/5000000000 : ℝ)*X 1 1+(2501655503/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2709425217/5000000000 : ℝ)*X 2 0+(5003309221/10000000000 : ℝ)*X 2 1+(-1235250789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317014607/10000000000 : ℝ)*X 0 0+(73559477/200000000 : ℝ)*X 0 1+(2532861853/5000000000 : ℝ)*X 0 2+(4317014607/10000000000 : ℝ)*X 1 0+(73559477/200000000 : ℝ)*X 1 1+(2532861853/5000000000 : ℝ)*X 1 2+(4317014607/10000000000 : ℝ)*X 2 0+(73559477/200000000 : ℝ)*X 2 1+(2532861853/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2095330931/10000000000 : ℝ)*X 0 0+(5012808397/10000000000 : ℝ)*X 0 1+(177827847/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5240140359/10000000000 : ℝ)*X 1 0+(-1783321673/10000000000 : ℝ)*X 1 1+(5690490717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1048028087/2000000000 : ℝ)*X 2 0+(5690490929/10000000000 : ℝ)*X 2 1+(-891660627/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((16869541/39062500 : ℝ)*X 0 0+(504681327/1000000000 : ℝ)*X 0 1+(147890357/400000000 : ℝ)*X 0 2+(16869541/39062500 : ℝ)*X 1 0+(504681327/1000000000 : ℝ)*X 1 1+(147890357/400000000 : ℝ)*X 1 2+(16869541/39062500 : ℝ)*X 2 0+(504681327/1000000000 : ℝ)*X 2 1+(147890357/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5949344805074062196171956599/684050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31723699/5000000000000 : ℝ)*(base1) + (47420101/3125000000000 : ℝ)*(base19) + (254005293/12500000000000 : ℝ)*(base23) + (16623913/100000000000000 : ℝ)*(base24) + (216944411/100000000000000 : ℝ)*(upper5) + (1077799074075517/100000000000000 : ℝ)*(major0) + (1077799074075517/100000000000000 : ℝ)*(major1) + (1077799074075517/100000000000000 : ℝ)*(major2) + (179375178266857/12500000000000 : ℝ)*(sp0) + (71750202353571/5000000000000 : ℝ)*(sp1) + (287000703169679/20000000000000 : ℝ)*(sp2) + (14411829957749/2000000000000 : ℝ)*(sp3) + (4772853777/100000000000000 : ℝ)*(sp4) + (80683527/50000000000000 : ℝ)*(sp7) + (144118458745697/20000000000000 : ℝ)*(f.failure) + (358751391128663/25000000000000 : ℝ)*(f.sum) + (352476379708663/136810000000000000000000000000 : ℝ)*base65 + (60796987515656489/1368100000000000000000000000000000 : ℝ)*base67 + (188476631508756489/1368100000000000000000000000000000 : ℝ)*base69 + (7235274778168356489/1368100000000000000000000000000000 : ℝ)*base71 + (245016244741813/136810000000000000000000000000 : ℝ)*base73 + (4243898851152756489/1368100000000000000000000000000000 : ℝ)*base75 + (8804176739041356489/1368100000000000000000000000000000 : ℝ)*base77 + (8037716484292256489/1368100000000000000000000000000000 : ℝ)*base79 + (532158613546813/136810000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1153989/1000000000000000000000 : ℝ)*base89 + (1153989/1000000000000000000000 : ℝ)*base91 + (1153989/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1593153098114209535034735141/171012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5971157/5000000000000 : ℝ)*(base1) + (409133061/20000000000000 : ℝ)*(base19) + (1047167649/50000000000000 : ℝ)*(base23) + (190943223/100000000000000 : ℝ)*(upper3) + (104394923/50000000000000 : ℝ)*(upper5) + (277075345749403/25000000000000 : ℝ)*(major0) + (277075345749403/25000000000000 : ℝ)*(major1) + (277075345749403/25000000000000 : ℝ)*(major2) + (8230367113/100000000000000 : ℝ)*(sp1) + (9029846597/100000000000000 : ℝ)*(sp2) + (2305651752119/156250000000 : ℝ)*(sp4) + (737803362950301/50000000000000 : ℝ)*(sp5) + (11804847022009/800000000000 : ℝ)*(sp6) + (370492667052799/50000000000000 : ℝ)*(sp7) + (370492726764369/50000000000000 : ℝ)*(f.failure) + (73780850096651/5000000000000 : ℝ)*(f.sum) + (45819098246947/34202500000000000000000000000 : ℝ)*base65 + (1106895869341219151/342025000000000000000000000000000 : ℝ)*base67 + (1018173965275969151/342025000000000000000000000000000 : ℝ)*base69 + (2145503995818469151/342025000000000000000000000000000 : ℝ)*base71 + (70820301617753/34202500000000000000000000000 : ℝ)*base74 + (285058197035169151/342025000000000000000000000000000 : ℝ)*base75 + (1878530228696694151/342025000000000000000000000000000 : ℝ)*base77 + (2529056155463669151/342025000000000000000000000000000 : ℝ)*base79 + (24779780525383/8550625000000000000000000000 : ℝ)*base81 + (15431947/2500000000000000000000 : ℝ)*base90 + (15431947/2500000000000000000000 : ℝ)*base92 + (15431947/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1147_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6949/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (217/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4083/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1147_s2_0 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2147494927/10000000000 : ℝ)*x 0 + (5509870437/10000000000 : ℝ)*x 1 + (5159933569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147494927/10000000000 : ℝ)^2085 ≤ (13016102035261/100000000000000 : ℝ)^1573 := by
    have hnat : (2147494927 : ℕ)^2085*100000000000000^1573 ≤ 13016102035261^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147494927 10000000000 13016102035261 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5509870437/10000000000 : ℝ)^2085 ≤ (4538212215901/10000000000000 : ℝ)^1573 := by
    have hnat : (5509870437 : ℕ)^2085*10000000000000^1573 ≤ 4538212215901^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5509870437 10000000000 4538212215901 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5159933569/10000000000 : ℝ)^2085 ≤ (41601775796387/100000000000000 : ℝ)^1573 := by
    have hnat : (5159933569 : ℕ)^2085*100000000000000^1573 ≤ 41601775796387^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5159933569 10000000000 41601775796387 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2147494927/10000000000 : ℝ), (5509870437/10000000000 : ℝ), (5159933569/10000000000 : ℝ)] ![(13016102035261/100000000000000 : ℝ), (4538212215901/10000000000000 : ℝ), (41601775796387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2147494927/10000000000 : ℝ)|^2085 ≤ (13016102035261/100000000000000 : ℝ)^1573
        have hw : |(-2147494927/10000000000 : ℝ)|=(2147494927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5509870437/10000000000 : ℝ)|^2085 ≤ (4538212215901/10000000000000 : ℝ)^1573
        have hw : |(5509870437/10000000000 : ℝ)|=(5509870437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5159933569/10000000000 : ℝ)|^2085 ≤ (41601775796387/100000000000000 : ℝ)^1573
        have hw : |(5159933569/10000000000 : ℝ)|=(5159933569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s2_1 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074730379/2000000000 : ℝ)*x 0 + (-2329392149/10000000000 : ℝ)*x 1 + (2579967873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074730379/2000000000 : ℝ)^2085 ≤ (21950490916229/50000000000000 : ℝ)^1573 := by
    have hnat : (1074730379 : ℕ)^2085*50000000000000^1573 ≤ 21950490916229^1573*2000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074730379 2000000000 21950490916229 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2329392149/10000000000 : ℝ)^2085 ≤ (1449721908483/10000000000000 : ℝ)^1573 := by
    have hnat : (2329392149 : ℕ)^2085*10000000000000^1573 ≤ 1449721908483^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2329392149 10000000000 1449721908483 10000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2579967873/5000000000 : ℝ)^2085 ≤ (41601799061413/100000000000000 : ℝ)^1573 := by
    have hnat : (2579967873 : ℕ)^2085*100000000000000^1573 ≤ 41601799061413^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579967873 5000000000 41601799061413 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074730379/2000000000 : ℝ), (-2329392149/10000000000 : ℝ), (2579967873/5000000000 : ℝ)] ![(21950490916229/50000000000000 : ℝ), (1449721908483/10000000000000 : ℝ), (41601799061413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074730379/2000000000 : ℝ)|^2085 ≤ (21950490916229/50000000000000 : ℝ)^1573
        have hw : |(1074730379/2000000000 : ℝ)|=(1074730379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2329392149/10000000000 : ℝ)|^2085 ≤ (1449721908483/10000000000000 : ℝ)^1573
        have hw : |(-2329392149/10000000000 : ℝ)|=(2329392149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2579967873/5000000000 : ℝ)|^2085 ≤ (41601799061413/100000000000000 : ℝ)^1573
        have hw : |(2579967873/5000000000 : ℝ)|=(2579967873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s2_2 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2686825977/5000000000 : ℝ)*x 0 + (10319871/20000000 : ℝ)*x 1 + (-291174049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686825977/5000000000 : ℝ)^2085 ≤ (137190570223/312500000000 : ℝ)^1573 := by
    have hnat : (2686825977 : ℕ)^2085*312500000000^1573 ≤ 137190570223^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686825977 5000000000 137190570223 312500000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10319871/20000000 : ℝ)^2085 ≤ (10400449108119/25000000000000 : ℝ)^1573 := by
    have hnat : (10319871 : ℕ)^2085*25000000000000^1573 ≤ 10400449108119^1573*20000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10319871 20000000 10400449108119 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (291174049/1250000000 : ℝ)^2085 ≤ (14497221089421/100000000000000 : ℝ)^1573 := by
    have hnat : (291174049 : ℕ)^2085*100000000000000^1573 ≤ 14497221089421^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291174049 1250000000 14497221089421 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686825977/5000000000 : ℝ), (10319871/20000000 : ℝ), (-291174049/1250000000 : ℝ)] ![(137190570223/312500000000 : ℝ), (10400449108119/25000000000000 : ℝ), (14497221089421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686825977/5000000000 : ℝ)|^2085 ≤ (137190570223/312500000000 : ℝ)^1573
        have hw : |(2686825977/5000000000 : ℝ)|=(2686825977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(10319871/20000000 : ℝ)|^2085 ≤ (10400449108119/25000000000000 : ℝ)^1573
        have hw : |(10319871/20000000 : ℝ)|=(10319871/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-291174049/1250000000 : ℝ)|^2085 ≤ (14497221089421/100000000000000 : ℝ)^1573
        have hw : |(-291174049/1250000000 : ℝ)|=(291174049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s2_3 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4353361701/10000000000 : ℝ)*x 0 + (502341287/1250000000 : ℝ)*x 1 + (94311973/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353361701/10000000000 : ℝ)^2085 ≤ (33209692134629/100000000000000 : ℝ)^1573 := by
    have hnat : (4353361701 : ℕ)^2085*100000000000000^1573 ≤ 33209692134629^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353361701 10000000000 33209692134629 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502341287/1250000000 : ℝ)^2085 ≤ (7467284331599/25000000000000 : ℝ)^1573 := by
    have hnat : (502341287 : ℕ)^2085*25000000000000^1573 ≤ 7467284331599^1573*1250000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502341287 1250000000 7467284331599 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94311973/200000000 : ℝ)^2085 ≤ (36921170521111/100000000000000 : ℝ)^1573 := by
    have hnat : (94311973 : ℕ)^2085*100000000000000^1573 ≤ 36921170521111^1573*200000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94311973 200000000 36921170521111 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353361701/10000000000 : ℝ), (502341287/1250000000 : ℝ), (94311973/200000000 : ℝ)] ![(33209692134629/100000000000000 : ℝ), (7467284331599/25000000000000 : ℝ), (36921170521111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353361701/10000000000 : ℝ)|^2085 ≤ (33209692134629/100000000000000 : ℝ)^1573
        have hw : |(4353361701/10000000000 : ℝ)|=(4353361701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502341287/1250000000 : ℝ)|^2085 ≤ (7467284331599/25000000000000 : ℝ)^1573
        have hw : |(502341287/1250000000 : ℝ)|=(502341287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(94311973/200000000 : ℝ)|^2085 ≤ (36921170521111/100000000000000 : ℝ)^1573
        have hw : |(94311973/200000000 : ℝ)|=(94311973/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s2_4 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073798113/5000000000 : ℝ)*x 0 + (5162338479/10000000000 : ℝ)*x 1 + (5507441449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073798113/5000000000 : ℝ)^2085 ≤ (13016915867007/100000000000000 : ℝ)^1573 := by
    have hnat : (1073798113 : ℕ)^2085*100000000000000^1573 ≤ 13016915867007^1573*5000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073798113 5000000000 13016915867007 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5162338479/10000000000 : ℝ)^2085 ≤ (10406869596189/25000000000000 : ℝ)^1573 := by
    have hnat : (5162338479 : ℕ)^2085*25000000000000^1573 ≤ 10406869596189^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5162338479 10000000000 10406869596189 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5507441449/10000000000 : ℝ)^2085 ≤ (9071121146977/20000000000000 : ℝ)^1573 := by
    have hnat : (5507441449 : ℕ)^2085*20000000000000^1573 ≤ 9071121146977^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507441449 10000000000 9071121146977 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073798113/5000000000 : ℝ), (5162338479/10000000000 : ℝ), (5507441449/10000000000 : ℝ)] ![(13016915867007/100000000000000 : ℝ), (10406869596189/25000000000000 : ℝ), (9071121146977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073798113/5000000000 : ℝ)|^2085 ≤ (13016915867007/100000000000000 : ℝ)^1573
        have hw : |(-1073798113/5000000000 : ℝ)|=(1073798113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5162338479/10000000000 : ℝ)|^2085 ≤ (10406869596189/25000000000000 : ℝ)^1573
        have hw : |(5162338479/10000000000 : ℝ)|=(5162338479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5507441449/10000000000 : ℝ)|^2085 ≤ (9071121146977/20000000000000 : ℝ)^1573
        have hw : |(5507441449/10000000000 : ℝ)|=(5507441449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s2_5 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5284834131/10000000000 : ℝ)*x 0 + (-495471063/2500000000 : ℝ)*x 1 + (1376860543/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284834131/10000000000 : ℝ)^2085 ≤ (5367723136229/12500000000000 : ℝ)^1573 := by
    have hnat : (5284834131 : ℕ)^2085*12500000000000^1573 ≤ 5367723136229^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284834131 10000000000 5367723136229 12500000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (495471063/2500000000 : ℝ)^2085 ≤ (2925650317937/25000000000000 : ℝ)^1573 := by
    have hnat : (495471063 : ℕ)^2085*25000000000000^1573 ≤ 2925650317937^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495471063 2500000000 2925650317937 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1376860543/2500000000 : ℝ)^2085 ≤ (2267780681353/5000000000000 : ℝ)^1573 := by
    have hnat : (1376860543 : ℕ)^2085*5000000000000^1573 ≤ 2267780681353^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376860543 2500000000 2267780681353 5000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284834131/10000000000 : ℝ), (-495471063/2500000000 : ℝ), (1376860543/2500000000 : ℝ)] ![(5367723136229/12500000000000 : ℝ), (2925650317937/25000000000000 : ℝ), (2267780681353/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284834131/10000000000 : ℝ)|^2085 ≤ (5367723136229/12500000000000 : ℝ)^1573
        have hw : |(5284834131/10000000000 : ℝ)|=(5284834131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-495471063/2500000000 : ℝ)|^2085 ≤ (2925650317937/25000000000000 : ℝ)^1573
        have hw : |(-495471063/2500000000 : ℝ)|=(495471063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1376860543/2500000000 : ℝ)|^2085 ≤ (2267780681353/5000000000000 : ℝ)^1573
        have hw : |(1376860543/2500000000 : ℝ)|=(1376860543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s2_6 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5284832539/10000000000 : ℝ)*x 0 + (5507441931/10000000000 : ℝ)*x 1 + (-1981886779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284832539/10000000000 : ℝ)^2085 ≤ (42941767943583/100000000000000 : ℝ)^1573 := by
    have hnat : (5284832539 : ℕ)^2085*100000000000000^1573 ≤ 42941767943583^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284832539 10000000000 42941767943583 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507441931/10000000000 : ℝ)^2085 ≤ (9071122199267/20000000000000 : ℝ)^1573 := by
    have hnat : (5507441931 : ℕ)^2085*20000000000000^1573 ≤ 9071122199267^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507441931 10000000000 9071122199267 20000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981886779/10000000000 : ℝ)^2085 ≤ (11702621049949/100000000000000 : ℝ)^1573 := by
    have hnat : (1981886779 : ℕ)^2085*100000000000000^1573 ≤ 11702621049949^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981886779 10000000000 11702621049949 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284832539/10000000000 : ℝ), (5507441931/10000000000 : ℝ), (-1981886779/10000000000 : ℝ)] ![(42941767943583/100000000000000 : ℝ), (9071122199267/20000000000000 : ℝ), (11702621049949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284832539/10000000000 : ℝ)|^2085 ≤ (42941767943583/100000000000000 : ℝ)^1573
        have hw : |(5284832539/10000000000 : ℝ)|=(5284832539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507441931/10000000000 : ℝ)|^2085 ≤ (9071122199267/20000000000000 : ℝ)^1573
        have hw : |(5507441931/10000000000 : ℝ)|=(5507441931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981886779/10000000000 : ℝ)|^2085 ≤ (11702621049949/100000000000000 : ℝ)^1573
        have hw : |(-1981886779/10000000000 : ℝ)|=(1981886779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1147_s2_7 (p : ℝ) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4353562381/10000000000 : ℝ)*x 0 + (1177702829/2500000000 : ℝ)*x 1 + (4023565653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4353562381/10000000000 : ℝ)^2085 ≤ (16605860667153/50000000000000 : ℝ)^1573 := by
    have hnat : (4353562381 : ℕ)^2085*50000000000000^1573 ≤ 16605860667153^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4353562381 10000000000 16605860667153 50000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177702829/2500000000 : ℝ)^2085 ≤ (36871495516751/100000000000000 : ℝ)^1573 := by
    have hnat : (1177702829 : ℕ)^2085*100000000000000^1573 ≤ 36871495516751^1573*2500000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177702829 2500000000 36871495516751 100000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4023565653/10000000000 : ℝ)^2085 ≤ (7479195783987/25000000000000 : ℝ)^1573 := by
    have hnat : (4023565653 : ℕ)^2085*25000000000000^1573 ≤ 7479195783987^1573*10000000000^2085 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023565653 10000000000 7479195783987 25000000000000 2085 1573 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2085/512 : ℝ)) 2085 1573 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4353562381/10000000000 : ℝ), (1177702829/2500000000 : ℝ), (4023565653/10000000000 : ℝ)] ![(16605860667153/50000000000000 : ℝ), (36871495516751/100000000000000 : ℝ), (7479195783987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4353562381/10000000000 : ℝ)|^2085 ≤ (16605860667153/50000000000000 : ℝ)^1573
        have hw : |(4353562381/10000000000 : ℝ)|=(4353562381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1177702829/2500000000 : ℝ)|^2085 ≤ (36871495516751/100000000000000 : ℝ)^1573
        have hw : |(1177702829/2500000000 : ℝ)|=(1177702829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4023565653/10000000000 : ℝ)|^2085 ≤ (7479195783987/25000000000000 : ℝ)^1573
        have hw : |(4023565653/10000000000 : ℝ)|=(4023565653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1147_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4083/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9093/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2061/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4083/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5677/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4083/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5677/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4083/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5677/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4083/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5677/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4083/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5677/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4083/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5677/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (5677/100000 : ℝ) ^ (8339/2048 : ℝ) ≤ (845375272648021/100000000000000000000 : ℝ) := by
    have hpowers : (5677/100000 : ℝ)^8339 ≤ (845375272648021/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5677 : ℕ)^8339*100000000000000000000^2048 ≤ 845375272648021^2048*100000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5677 100000 845375272648021 100000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5677/100000 : ℝ)) (X := (845375272648021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4083/20000 : ℝ) ^ (8339/2048 : ℝ) ≤ (77488551224424957/50000000000000000000 : ℝ) := by
    have hpowers : (4083/20000 : ℝ)^8339 ≤ (77488551224424957/50000000000000000000 : ℝ)^2048 := by
      have hnat : (4083 : ℕ)^8339*50000000000000000000^2048 ≤ 77488551224424957^2048*20000^8339 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4083 20000 77488551224424957 50000000000000000000 8339 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4083/20000 : ℝ)) (X := (77488551224424957/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000845375272648021/50000000000000000000 : ℝ) ≤ (10000041523384503/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (50000845375272648021/50000000000000000000 : ℝ)^2048 ≤ (10000041523384503/10000000000000000 : ℝ)^8339 := by
      have hnat : (50000845375272648021 : ℕ)^2048*10000000000000000^8339 ≤ 10000041523384503^8339*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000845375272648021 50000000000000000000 10000041523384503 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000041523384503/10000000000000000 : ℝ)) (X := (50000845375272648021/50000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20031164495544299587/20000000000000000000 : ℝ) ≤ (5001912321825369/5000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (20031164495544299587/20000000000000000000 : ℝ)^2048 ≤ (5001912321825369/5000000000000000 : ℝ)^8339 := by
      have hnat : (20031164495544299587 : ℕ)^2048*5000000000000000^8339 ≤ 5001912321825369^8339*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20031164495544299587 20000000000000000000 5001912321825369 5000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001912321825369/5000000000000000 : ℝ)) (X := (20031164495544299587/20000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25077488551224424957/25000000000000000000 : ℝ) ≤ (10007607763916973/10000000000000000 : ℝ) ^ (8339/2048 : ℝ) := by
    have hpowers : (25077488551224424957/25000000000000000000 : ℝ)^2048 ≤ (10007607763916973/10000000000000000 : ℝ)^8339 := by
      have hnat : (25077488551224424957 : ℕ)^2048*10000000000000000^8339 ≤ 10007607763916973^8339*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25077488551224424957 25000000000000000000 10007607763916973 10000000000000000 2048 8339 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007607763916973/10000000000000000 : ℝ)) (X := (25077488551224424957/25000000000000000000 : ℝ)) (by norm_num) 8339 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(845375272648021/100000000000000000000 : ℝ) ≤ ((4604301825754311657/4605625000000000000 : ℝ)+2*(756624053247/294760000000000 : ℝ)*(5677/100000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (4604301825754311657/4605625000000000000 : ℝ)+2*(756624053247/294760000000000 : ℝ)*(5677/100000 : ℝ)=(10000041523384503/10000000000000000 : ℝ) by norm_num, show 1+2*(845375272648021/100000000000000000000 : ℝ)=(50000845375272648021/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(77488551224424957/50000000000000000000 : ℝ)+(845375272648021/100000000000000000000 : ℝ) ≤ ((4604301825754311657/4605625000000000000 : ℝ)+(756624053247/294760000000000 : ℝ)*((4083/20000 : ℝ)+(5677/100000 : ℝ)))^(8339/2048 : ℝ) := by
    rw [show (4604301825754311657/4605625000000000000 : ℝ)+(756624053247/294760000000000 : ℝ)*((4083/20000 : ℝ)+(5677/100000 : ℝ))=(5001912321825369/5000000000000000 : ℝ) by norm_num, show 1+(77488551224424957/50000000000000000000 : ℝ)+(845375272648021/100000000000000000000 : ℝ)=(20031164495544299587/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(77488551224424957/50000000000000000000 : ℝ) ≤ ((4604301825754311657/4605625000000000000 : ℝ)+2*(756624053247/294760000000000 : ℝ)*(4083/20000 : ℝ))^(8339/2048 : ℝ) := by
    rw [show (4604301825754311657/4605625000000000000 : ℝ)+2*(756624053247/294760000000000 : ℝ)*(4083/20000 : ℝ)=(10007607763916973/10000000000000000 : ℝ) by norm_num, show 1+2*(77488551224424957/50000000000000000000 : ℝ)=(25077488551224424957/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4604301825754311657/4605625000000000000 : ℝ)*(X 1 0+X 2 0)+(756624053247/294760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (5677/100000 : ℝ)) (hi := (4083/20000 : ℝ)) (c := (4604301825754311657/4605625000000000000 : ℝ)) (alpha := (756624053247/294760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4604301825754311657/4605625000000000000 : ℝ)*(X 0 1+X 2 1)+(756624053247/294760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (5677/100000 : ℝ)) (hi := (4083/20000 : ℝ)) (c := (4604301825754311657/4605625000000000000 : ℝ)) (alpha := (756624053247/294760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4604301825754311657/4605625000000000000 : ℝ)*(X 0 2+X 1 2)+(756624053247/294760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8339/2048 : ℝ)) (lo := (5677/100000 : ℝ)) (hi := (4083/20000 : ℝ)) (c := (4604301825754311657/4605625000000000000 : ℝ)) (alpha := (756624053247/294760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2147494927/10000000000 : ℝ)*X 0 0+(5509870437/10000000000 : ℝ)*X 0 1+(5159933569/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1074730379/2000000000 : ℝ)*X 1 0+(-2329392149/10000000000 : ℝ)*X 1 1+(2579967873/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2686825977/5000000000 : ℝ)*X 2 0+(10319871/20000000 : ℝ)*X 2 1+(-291174049/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4353361701/10000000000 : ℝ)*X 0 0+(502341287/1250000000 : ℝ)*X 0 1+(94311973/200000000 : ℝ)*X 0 2+(4353361701/10000000000 : ℝ)*X 1 0+(502341287/1250000000 : ℝ)*X 1 1+(94311973/200000000 : ℝ)*X 1 2+(4353361701/10000000000 : ℝ)*X 2 0+(502341287/1250000000 : ℝ)*X 2 1+(94311973/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1073798113/5000000000 : ℝ)*X 0 0+(5162338479/10000000000 : ℝ)*X 0 1+(5507441449/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5284834131/10000000000 : ℝ)*X 1 0+(-495471063/2500000000 : ℝ)*X 1 1+(1376860543/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5284832539/10000000000 : ℝ)*X 2 0+(5507441931/10000000000 : ℝ)*X 2 1+(-1981886779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4353562381/10000000000 : ℝ)*X 0 0+(1177702829/2500000000 : ℝ)*X 0 1+(4023565653/10000000000 : ℝ)*X 0 2+(4353562381/10000000000 : ℝ)*X 1 0+(1177702829/2500000000 : ℝ)*X 1 1+(4023565653/10000000000 : ℝ)*X 1 2+(4353562381/10000000000 : ℝ)*X 2 0+(1177702829/2500000000 : ℝ)*X 2 1+(4023565653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1147_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (309980544574454610362977407/115140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (315241759/100000000000000 : ℝ)*(base15) + (91876727/50000000000000 : ℝ)*(upper2) + (19775749/25000000000000 : ℝ)*(upper3) + (52949657/100000000000000 : ℝ)*(upper4) + (429268006473217/20000000000000 : ℝ)*(major0) + (429268006473217/20000000000000 : ℝ)*(major1) + (1073170016183043/50000000000000 : ℝ)*(major2) + (2857674211014173/100000000000000 : ℝ)*(sp0) + (2857684840915317/100000000000000 : ℝ)*(sp1) + (714421237746179/25000000000000 : ℝ)*(sp2) + (1434993438176241/100000000000000 : ℝ)*(sp3) + (10945142903/100000000000000 : ℝ)*(sp4) + (5129309/2500000000000 : ℝ)*(sp6) + (1380659149/100000000000000 : ℝ)*(sp7) + (143499481883539/10000000000000 : ℝ)*(f.failure) + (714421289039269/25000000000000 : ℝ)*(f.sum) + (229392019756001/29476000000000000000000000000 : ℝ)*base65 + (1171449143728503181/92112500000000000000000000000000 : ℝ)*base68 + (760765498546248877/460562500000000000000000000000000 : ℝ)*base69 + (902517476477540681/92112500000000000000000000000000 : ℝ)*base72 + (1420844753649/1179040000000000000000000000 : ℝ)*base73 + (1894043272567373877/460562500000000000000000000000000 : ℝ)*base75 + (7841558729775007/11514062500000000000000000000000 : ℝ)*base78 + (54253903505242191/5757031250000000000000000000000 : ℝ)*base80 + (732842121953/2947600000000000000000000000 : ℝ)*base81 + (1070657/500000000000000000000 : ℝ)*base90 + (1070657/500000000000000000000 : ℝ)*base92 + (6070657/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (512577182943795303804909153/57570312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (763963757/50000000000000 : ℝ)*(base19) + (490074983/50000000000000 : ℝ)*(base23) + (348433223/100000000000000 : ℝ)*(upper2) + (17673741/20000000000000 : ℝ)*(upper3) + (282091313/100000000000000 : ℝ)*(upper5) + (544094958556591/25000000000000 : ℝ)*(major0) + (544094958556591/25000000000000 : ℝ)*(major1) + (544094958556591/25000000000000 : ℝ)*(major2) + (23238818449/100000000000000 : ℝ)*(sp1) + (3353773009/100000000000000 : ℝ)*(sp2) + (579536122976931/20000000000000 : ℝ)*(sp4) + (724413962034673/25000000000000 : ℝ)*(sp5) + (36220953512021/1250000000000 : ℝ)*(sp6) + (90942422299049/6250000000000 : ℝ)*(sp7) + (90942422299049/6250000000000 : ℝ)*(f.failure) + (579536122976931/20000000000000 : ℝ)*(f.sum) + (1644177646039/230281250000000000000000000 : ℝ)*base65 + (300576478349893713/115140625000000000000000000000000 : ℝ)*base68 + (1248982189011012537/115140625000000000000000000000000 : ℝ)*base69 + (668474341987325037/115140625000000000000000000000000 : ℝ)*base71 + (8459716200417/7369000000000000000000000000 : ℝ)*base74 + (364041165241232831/57570312500000000000000000000000 : ℝ)*base75 + (482290306173107831/57570312500000000000000000000000 : ℝ)*base77 + (15126595724577353/28785156250000000000000000000000 : ℝ)*base79 + (14052383135589/3684500000000000000000000000 : ℝ)*base81 + (3540787/312500000000000000000 : ℝ)*base90 + (3540787/312500000000000000000 : ℝ)*base92 + (3540787/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1147_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4083/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9093/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2061/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1147_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1147_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9093/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2061/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1147_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1147_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1147_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8339/2048 : ℝ) ≤ p) (hpb : p ≤ (2085/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74785637/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9093/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2061/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1147_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
