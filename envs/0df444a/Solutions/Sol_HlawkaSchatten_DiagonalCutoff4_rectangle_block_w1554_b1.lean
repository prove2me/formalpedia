-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1554_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:11:19.042457+00:00
-- url     : https://prove2.me/submissions/1b963b78-db90-49f6-95b7-87c2c19ade36

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
theorem support_rectangle_w1554_s3_0 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-903702967/5000000000 : ℝ)*x 0 + (2714920007/5000000000 : ℝ)*x 1 + (5217672303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903702967/5000000000 : ℝ)^4605 ≤ (2216348603863/20000000000000 : ℝ)^3581 := by
    have hnat : (903702967 : ℕ)^4605*20000000000000^3581 ≤ 2216348603863^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903702967 5000000000 2216348603863 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714920007/5000000000 : ℝ)^4605 ≤ (45598275624399/100000000000000 : ℝ)^3581 := by
    have hnat : (2714920007 : ℕ)^4605*100000000000000^3581 ≤ 45598275624399^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714920007 5000000000 45598275624399 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217672303/10000000000 : ℝ)^4605 ≤ (43319981346669/100000000000000 : ℝ)^3581 := by
    have hnat : (5217672303 : ℕ)^4605*100000000000000^3581 ≤ 43319981346669^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217672303 10000000000 43319981346669 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903702967/5000000000 : ℝ), (2714920007/5000000000 : ℝ), (5217672303/10000000000 : ℝ)] ![(2216348603863/20000000000000 : ℝ), (45598275624399/100000000000000 : ℝ), (43319981346669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903702967/5000000000 : ℝ)|^4605 ≤ (2216348603863/20000000000000 : ℝ)^3581
        have hw : |(-903702967/5000000000 : ℝ)|=(903702967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714920007/5000000000 : ℝ)|^4605 ≤ (45598275624399/100000000000000 : ℝ)^3581
        have hw : |(2714920007/5000000000 : ℝ)|=(2714920007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217672303/10000000000 : ℝ)|^4605 ≤ (43319981346669/100000000000000 : ℝ)^3581
        have hw : |(5217672303/10000000000 : ℝ)|=(5217672303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s3_1 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534969377/1000000000 : ℝ)*x 0 + (-1916025323/10000000000 : ℝ)*x 1 + (5217672299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534969377/1000000000 : ℝ)^4605 ≤ (22367301524979/50000000000000 : ℝ)^3581 := by
    have hnat : (534969377 : ℕ)^4605*50000000000000^3581 ≤ 22367301524979^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534969377 1000000000 22367301524979 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1916025323/10000000000 : ℝ)^4605 ≤ (5972707817211/50000000000000 : ℝ)^3581 := by
    have hnat : (1916025323 : ℕ)^4605*50000000000000^3581 ≤ 5972707817211^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916025323 10000000000 5972707817211 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217672299/10000000000 : ℝ)^4605 ≤ (21659990651981/50000000000000 : ℝ)^3581 := by
    have hnat : (5217672299 : ℕ)^4605*50000000000000^3581 ≤ 21659990651981^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217672299 10000000000 21659990651981 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534969377/1000000000 : ℝ), (-1916025323/10000000000 : ℝ), (5217672299/10000000000 : ℝ)] ![(22367301524979/50000000000000 : ℝ), (5972707817211/50000000000000 : ℝ), (21659990651981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534969377/1000000000 : ℝ)|^4605 ≤ (22367301524979/50000000000000 : ℝ)^3581
        have hw : |(534969377/1000000000 : ℝ)|=(534969377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1916025323/10000000000 : ℝ)|^4605 ≤ (5972707817211/50000000000000 : ℝ)^3581
        have hw : |(-1916025323/10000000000 : ℝ)|=(1916025323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217672299/10000000000 : ℝ)|^4605 ≤ (21659990651981/50000000000000 : ℝ)^3581
        have hw : |(5217672299/10000000000 : ℝ)|=(5217672299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s3_2 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674846897/5000000000 : ℝ)*x 0 + (5217672239/10000000000 : ℝ)*x 1 + (-1916025371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674846897/5000000000 : ℝ)^4605 ≤ (44734603308037/100000000000000 : ℝ)^3581 := by
    have hnat : (2674846897 : ℕ)^4605*100000000000000^3581 ≤ 44734603308037^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674846897 5000000000 44734603308037 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217672239/10000000000 : ℝ)^4605 ≤ (43319980663361/100000000000000 : ℝ)^3581 := by
    have hnat : (5217672239 : ℕ)^4605*100000000000000^3581 ≤ 43319980663361^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217672239 10000000000 43319980663361 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1916025371/10000000000 : ℝ)^4605 ≤ (47781664077/400000000000 : ℝ)^3581 := by
    have hnat : (1916025371 : ℕ)^4605*400000000000^3581 ≤ 47781664077^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1916025371 10000000000 47781664077 400000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674846897/5000000000 : ℝ), (5217672239/10000000000 : ℝ), (-1916025371/10000000000 : ℝ)] ![(44734603308037/100000000000000 : ℝ), (43319980663361/100000000000000 : ℝ), (47781664077/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674846897/5000000000 : ℝ)|^4605 ≤ (44734603308037/100000000000000 : ℝ)^3581
        have hw : |(2674846897/5000000000 : ℝ)|=(2674846897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217672239/10000000000 : ℝ)|^4605 ≤ (43319980663361/100000000000000 : ℝ)^3581
        have hw : |(5217672239/10000000000 : ℝ)|=(5217672239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1916025371/10000000000 : ℝ)|^4605 ≤ (47781664077/400000000000 : ℝ)^3581
        have hw : |(-1916025371/10000000000 : ℝ)|=(1916025371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s3_3 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125207703/5000000000 : ℝ)*x 0 + (1002161249/2500000000 : ℝ)*x 1 + (4504025799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125207703/5000000000 : ℝ)^4605 ≤ (33279743873263/100000000000000 : ℝ)^3581 := by
    have hnat : (2125207703 : ℕ)^4605*100000000000000^3581 ≤ 33279743873263^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125207703 5000000000 33279743873263 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1002161249/2500000000 : ℝ)^4605 ≤ (1234619989961/4000000000000 : ℝ)^3581 := by
    have hnat : (1002161249 : ℕ)^4605*4000000000000^3581 ≤ 1234619989961^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1002161249 2500000000 1234619989961 4000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504025799/10000000000 : ℝ)^4605 ≤ (17927378180831/50000000000000 : ℝ)^3581 := by
    have hnat : (4504025799 : ℕ)^4605*50000000000000^3581 ≤ 17927378180831^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504025799 10000000000 17927378180831 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125207703/5000000000 : ℝ), (1002161249/2500000000 : ℝ), (4504025799/10000000000 : ℝ)] ![(33279743873263/100000000000000 : ℝ), (1234619989961/4000000000000 : ℝ), (17927378180831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125207703/5000000000 : ℝ)|^4605 ≤ (33279743873263/100000000000000 : ℝ)^3581
        have hw : |(2125207703/5000000000 : ℝ)|=(2125207703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1002161249/2500000000 : ℝ)|^4605 ≤ (1234619989961/4000000000000 : ℝ)^3581
        have hw : |(1002161249/2500000000 : ℝ)|=(1002161249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504025799/10000000000 : ℝ)|^4605 ≤ (17927378180831/50000000000000 : ℝ)^3581
        have hw : |(4504025799/10000000000 : ℝ)|=(4504025799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s3_4 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-903717457/5000000000 : ℝ)*x 0 + (208751751/400000000 : ℝ)*x 1 + (678588753/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (903717457/5000000000 : ℝ)^4605 ≤ (2216394302901/20000000000000 : ℝ)^3581 := by
    have hnat : (903717457 : ℕ)^4605*20000000000000^3581 ≤ 2216394302901^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903717457 5000000000 2216394302901 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208751751/400000000 : ℝ)^4605 ≤ (43331955327407/100000000000000 : ℝ)^3581 := by
    have hnat : (208751751 : ℕ)^4605*100000000000000^3581 ≤ 43331955327407^3581*400000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208751751 400000000 43331955327407 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678588753/1250000000 : ℝ)^4605 ≤ (1139651828419/2500000000000 : ℝ)^3581 := by
    have hnat : (678588753 : ℕ)^4605*2500000000000^3581 ≤ 1139651828419^3581*1250000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678588753 1250000000 1139651828419 2500000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-903717457/5000000000 : ℝ), (208751751/400000000 : ℝ), (678588753/1250000000 : ℝ)] ![(2216394302901/20000000000000 : ℝ), (43331955327407/100000000000000 : ℝ), (1139651828419/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-903717457/5000000000 : ℝ)|^4605 ≤ (2216394302901/20000000000000 : ℝ)^3581
        have hw : |(-903717457/5000000000 : ℝ)|=(903717457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208751751/400000000 : ℝ)|^4605 ≤ (43331955327407/100000000000000 : ℝ)^3581
        have hw : |(208751751/400000000 : ℝ)|=(208751751/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678588753/1250000000 : ℝ)|^4605 ≤ (1139651828419/2500000000000 : ℝ)^3581
        have hw : |(678588753/1250000000 : ℝ)|=(678588753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s3_5 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293670611/10000000000 : ℝ)*x 0 + (-1704987449/10000000000 : ℝ)*x 1 + (217148401/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293670611/10000000000 : ℝ)^4605 ≤ (11033268989349/25000000000000 : ℝ)^3581 := by
    have hnat : (5293670611 : ℕ)^4605*25000000000000^3581 ≤ 11033268989349^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293670611 10000000000 11033268989349 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1704987449/10000000000 : ℝ)^4605 ≤ (10280850877309/100000000000000 : ℝ)^3581 := by
    have hnat : (1704987449 : ℕ)^4605*100000000000000^3581 ≤ 10280850877309^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1704987449 10000000000 10280850877309 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217148401/400000000 : ℝ)^4605 ≤ (22793036573779/50000000000000 : ℝ)^3581 := by
    have hnat : (217148401 : ℕ)^4605*50000000000000^3581 ≤ 22793036573779^3581*400000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217148401 400000000 22793036573779 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293670611/10000000000 : ℝ), (-1704987449/10000000000 : ℝ), (217148401/400000000 : ℝ)] ![(11033268989349/25000000000000 : ℝ), (10280850877309/100000000000000 : ℝ), (22793036573779/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293670611/10000000000 : ℝ)|^4605 ≤ (11033268989349/25000000000000 : ℝ)^3581
        have hw : |(5293670611/10000000000 : ℝ)|=(5293670611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1704987449/10000000000 : ℝ)|^4605 ≤ (10280850877309/100000000000000 : ℝ)^3581
        have hw : |(-1704987449/10000000000 : ℝ)|=(1704987449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217148401/400000000 : ℝ)|^4605 ≤ (22793036573779/50000000000000 : ℝ)^3581
        have hw : |(217148401/400000000 : ℝ)|=(217148401/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s3_6 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293670343/10000000000 : ℝ)*x 0 + (2714355069/5000000000 : ℝ)*x 1 + (-852493831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293670343/10000000000 : ℝ)^4605 ≤ (22066536542093/50000000000000 : ℝ)^3581 := by
    have hnat : (5293670343 : ℕ)^4605*50000000000000^3581 ≤ 22066536542093^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293670343 10000000000 22066536542093 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714355069/5000000000 : ℝ)^4605 ≤ (22793037183891/50000000000000 : ℝ)^3581 := by
    have hnat : (2714355069 : ℕ)^4605*50000000000000^3581 ≤ 22793037183891^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714355069 5000000000 22793037183891 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852493831/5000000000 : ℝ)^4605 ≤ (10280852528939/100000000000000 : ℝ)^3581 := by
    have hnat : (852493831 : ℕ)^4605*100000000000000^3581 ≤ 10280852528939^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852493831 5000000000 10280852528939 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293670343/10000000000 : ℝ), (2714355069/5000000000 : ℝ), (-852493831/5000000000 : ℝ)] ![(22066536542093/50000000000000 : ℝ), (22793037183891/50000000000000 : ℝ), (10280852528939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293670343/10000000000 : ℝ)|^4605 ≤ (22066536542093/50000000000000 : ℝ)^3581
        have hw : |(5293670343/10000000000 : ℝ)|=(5293670343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714355069/5000000000 : ℝ)|^4605 ≤ (22793037183891/50000000000000 : ℝ)^3581
        have hw : |(2714355069/5000000000 : ℝ)|=(2714355069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-852493831/5000000000 : ℝ)|^4605 ≤ (10280852528939/100000000000000 : ℝ)^3581
        have hw : |(-852493831/5000000000 : ℝ)|=(852493831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s3_7 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4250482867/10000000000 : ℝ)*x 0 + (2250703487/5000000000 : ℝ)*x 1 + (2005641737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4250482867/10000000000 : ℝ)^4605 ≤ (16640211560087/50000000000000 : ℝ)^3581 := by
    have hnat : (4250482867 : ℕ)^4605*50000000000000^3581 ≤ 16640211560087^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250482867 10000000000 16640211560087 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250703487/5000000000 : ℝ)^4605 ≤ (35827949770707/100000000000000 : ℝ)^3581 := by
    have hnat : (2250703487 : ℕ)^4605*100000000000000^3581 ≤ 35827949770707^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250703487 5000000000 35827949770707 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2005641737/5000000000 : ℝ)^4605 ≤ (7722906774841/25000000000000 : ℝ)^3581 := by
    have hnat : (2005641737 : ℕ)^4605*25000000000000^3581 ≤ 7722906774841^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005641737 5000000000 7722906774841 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4250482867/10000000000 : ℝ), (2250703487/5000000000 : ℝ), (2005641737/5000000000 : ℝ)] ![(16640211560087/50000000000000 : ℝ), (35827949770707/100000000000000 : ℝ), (7722906774841/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4250482867/10000000000 : ℝ)|^4605 ≤ (16640211560087/50000000000000 : ℝ)^3581
        have hw : |(4250482867/10000000000 : ℝ)|=(4250482867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250703487/5000000000 : ℝ)|^4605 ≤ (35827949770707/100000000000000 : ℝ)^3581
        have hw : |(2250703487/5000000000 : ℝ)|=(2250703487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2005641737/5000000000 : ℝ)|^4605 ≤ (7722906774841/25000000000000 : ℝ)^3581
        have hw : |(2005641737/5000000000 : ℝ)|=(2005641737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1554_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (991/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11029/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15527/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (991/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5363/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (991/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5363/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (991/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5363/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (991/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5363/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (991/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5363/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (991/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5363/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5363/50000 : ℝ) ^ (4603/1024 : ℝ) ≤ (1095580429925707/25000000000000000000 : ℝ) := by
    have hpowers : (5363/50000 : ℝ)^4603 ≤ (1095580429925707/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5363 : ℕ)^4603*25000000000000000000^1024 ≤ 1095580429925707^1024*50000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5363 50000 1095580429925707 25000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5363/50000 : ℝ)) (X := (1095580429925707/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (991/6250 : ℝ) ^ (4603/1024 : ℝ) ≤ (12698331952907863/50000000000000000000 : ℝ) := by
    have hpowers : (991/6250 : ℝ)^4603 ≤ (12698331952907863/50000000000000000000 : ℝ)^1024 := by
      have hnat : (991 : ℕ)^4603*50000000000000000000^1024 ≤ 12698331952907863^1024*6250^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        991 6250 12698331952907863 50000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (991/6250 : ℝ)) (X := (12698331952907863/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501095580429925707/12500000000000000000 : ℝ) ≤ (10000194974779113/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (12501095580429925707/12500000000000000000 : ℝ)^1024 ≤ (10000194974779113/10000000000000000 : ℝ)^4603 := by
      have hnat : (12501095580429925707 : ℕ)^1024*10000000000000000^4603 ≤ 10000194974779113^4603*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501095580429925707 12500000000000000000 10000194974779113 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000194974779113/10000000000000000 : ℝ)) (X := (12501095580429925707/12500000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014889492812759277/50000000000000000000 : ℝ) ≤ (5000331198692293/5000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (50014889492812759277/50000000000000000000 : ℝ)^1024 ≤ (5000331198692293/5000000000000000 : ℝ)^4603 := by
      have hnat : (50014889492812759277 : ℕ)^1024*5000000000000000^4603 ≤ 5000331198692293^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014889492812759277 50000000000000000000 5000331198692293 5000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000331198692293/5000000000000000 : ℝ)) (X := (50014889492812759277/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25012698331952907863/25000000000000000000 : ℝ) ≤ (10001129819990059/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (25012698331952907863/25000000000000000000 : ℝ)^1024 ≤ (10001129819990059/10000000000000000 : ℝ)^4603 := by
      have hnat : (25012698331952907863 : ℕ)^1024*10000000000000000^4603 ≤ 10001129819990059^4603*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012698331952907863 25000000000000000000 10001129819990059 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001129819990059/10000000000000000 : ℝ)) (X := (25012698331952907863/25000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1095580429925707/25000000000000000000 : ℝ) ≤ ((25645486535442121447/25650000000000000000 : ℝ)+2*(467422605473/513000000000000 : ℝ)*(5363/50000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (25645486535442121447/25650000000000000000 : ℝ)+2*(467422605473/513000000000000 : ℝ)*(5363/50000 : ℝ)=(10000194974779113/10000000000000000 : ℝ) by norm_num, show 1+2*(1095580429925707/25000000000000000000 : ℝ)=(12501095580429925707/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(12698331952907863/50000000000000000000 : ℝ)+(1095580429925707/25000000000000000000 : ℝ) ≤ ((25645486535442121447/25650000000000000000 : ℝ)+(467422605473/513000000000000 : ℝ)*((991/6250 : ℝ)+(5363/50000 : ℝ)))^(4603/1024 : ℝ) := by
    rw [show (25645486535442121447/25650000000000000000 : ℝ)+(467422605473/513000000000000 : ℝ)*((991/6250 : ℝ)+(5363/50000 : ℝ))=(5000331198692293/5000000000000000 : ℝ) by norm_num, show 1+(12698331952907863/50000000000000000000 : ℝ)+(1095580429925707/25000000000000000000 : ℝ)=(50014889492812759277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(12698331952907863/50000000000000000000 : ℝ) ≤ ((25645486535442121447/25650000000000000000 : ℝ)+2*(467422605473/513000000000000 : ℝ)*(991/6250 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (25645486535442121447/25650000000000000000 : ℝ)+2*(467422605473/513000000000000 : ℝ)*(991/6250 : ℝ)=(10001129819990059/10000000000000000 : ℝ) by norm_num, show 1+2*(12698331952907863/50000000000000000000 : ℝ)=(25012698331952907863/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25645486535442121447/25650000000000000000 : ℝ)*(X 1 0+X 2 0)+(467422605473/513000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (5363/50000 : ℝ)) (hi := (991/6250 : ℝ)) (c := (25645486535442121447/25650000000000000000 : ℝ)) (alpha := (467422605473/513000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25645486535442121447/25650000000000000000 : ℝ)*(X 0 1+X 2 1)+(467422605473/513000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (5363/50000 : ℝ)) (hi := (991/6250 : ℝ)) (c := (25645486535442121447/25650000000000000000 : ℝ)) (alpha := (467422605473/513000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25645486535442121447/25650000000000000000 : ℝ)*(X 0 2+X 1 2)+(467422605473/513000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (5363/50000 : ℝ)) (hi := (991/6250 : ℝ)) (c := (25645486535442121447/25650000000000000000 : ℝ)) (alpha := (467422605473/513000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-903702967/5000000000 : ℝ)*X 0 0+(2714920007/5000000000 : ℝ)*X 0 1+(5217672303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534969377/1000000000 : ℝ)*X 1 0+(-1916025323/10000000000 : ℝ)*X 1 1+(5217672299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674846897/5000000000 : ℝ)*X 2 0+(5217672239/10000000000 : ℝ)*X 2 1+(-1916025371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125207703/5000000000 : ℝ)*X 0 0+(1002161249/2500000000 : ℝ)*X 0 1+(4504025799/10000000000 : ℝ)*X 0 2+(2125207703/5000000000 : ℝ)*X 1 0+(1002161249/2500000000 : ℝ)*X 1 1+(4504025799/10000000000 : ℝ)*X 1 2+(2125207703/5000000000 : ℝ)*X 2 0+(1002161249/2500000000 : ℝ)*X 2 1+(4504025799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-903717457/5000000000 : ℝ)*X 0 0+(208751751/400000000 : ℝ)*X 0 1+(678588753/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293670611/10000000000 : ℝ)*X 1 0+(-1704987449/10000000000 : ℝ)*X 1 1+(217148401/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293670343/10000000000 : ℝ)*X 2 0+(2714355069/5000000000 : ℝ)*X 2 1+(-852493831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4250482867/10000000000 : ℝ)*X 0 0+(2250703487/5000000000 : ℝ)*X 0 1+(2005641737/5000000000 : ℝ)*X 0 2+(4250482867/10000000000 : ℝ)*X 1 0+(2250703487/5000000000 : ℝ)*X 1 1+(2005641737/5000000000 : ℝ)*X 1 2+(4250482867/10000000000 : ℝ)*X 2 0+(2250703487/5000000000 : ℝ)*X 2 1+(2005641737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1566915555856909841448947257/142500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1805290649/100000000000000 : ℝ)*(base19) + (1643993571/100000000000000 : ℝ)*(base23) + (19520187/20000000000000 : ℝ)*(lower2) + (295285569/100000000000000 : ℝ)*(upper3) + (118829109/100000000000000 : ℝ)*(upper5) + (3365991786242307/100000000000000 : ℝ)*(major0) + (3365991786242307/100000000000000 : ℝ)*(major1) + (3365991786242307/100000000000000 : ℝ)*(major2) + (4713282418765513/100000000000000 : ℝ)*(sp0) + (2356653720885683/50000000000000 : ℝ)*(sp1) + (1178326900767111/25000000000000 : ℝ)*(sp2) + (1009330101735117/50000000000000 : ℝ)*(sp3) + (26828296501/100000000000000 : ℝ)*(sp4) + (13755422403/100000000000000 : ℝ)*(sp7) + (1009336979446319/50000000000000 : ℝ)*(f.failure) + (942661849412403/20000000000000 : ℝ)*(f.sum) + (9000595264787/8550000000000000000000000000 : ℝ)*base65 + (5432471808493002743/855000000000000000000000000000000 : ℝ)*base67 + (3658738904653002743/855000000000000000000000000000000 : ℝ)*base69 + (6669931962883002743/855000000000000000000000000000000 : ℝ)*base71 + (43598324002337/8550000000000000000000000000 : ℝ)*base73 + (971152760551997257/855000000000000000000000000000000 : ℝ)*base76 + (1737055020703002743/855000000000000000000000000000000 : ℝ)*base77 + (4170894739951997257/855000000000000000000000000000000 : ℝ)*base80 + (2151721091537/8550000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (14065601/1250000000000000000000 : ℝ)*base89 + (14065601/1250000000000000000000 : ℝ)*base91 + (14065601/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (319692953219658373250948671/42750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1359184287/100000000000000 : ℝ)*(base19) + (1121196169/100000000000000 : ℝ)*(base23) + (67011509/50000000000000 : ℝ)*(upper3) + (17647627/50000000000000 : ℝ)*(lower4) + (49079051/25000000000000 : ℝ)*(upper5) + (340205247010393/10000000000000 : ℝ)*(major0) + (340205247010393/10000000000000 : ℝ)*(major1) + (340205247010393/10000000000000 : ℝ)*(major2) + (23113209327/100000000000000 : ℝ)*(sp1) + (2139262587/12500000000000 : ℝ)*(sp2) + (4763804189829691/100000000000000 : ℝ)*(sp4) + (4763779717436077/100000000000000 : ℝ)*(sp5) + (4763785954532827/100000000000000 : ℝ)*(sp6) + (1020150250552453/50000000000000 : ℝ)*(sp7) + (1020150250552453/50000000000000 : ℝ)*(f.failure) + (4763804189829691/100000000000000 : ℝ)*(f.sum) + (6532232955569/2565000000000000000000000000 : ℝ)*base65 + (1549977247626851329/256500000000000000000000000000000 : ℝ)*base68 + (525633739760351329/256500000000000000000000000000000 : ℝ)*base70 + (237242067968148671/256500000000000000000000000000000 : ℝ)*base71 + (4245936345361/2565000000000000000000000000 : ℝ)*base74 + (1372881247998648671/256500000000000000000000000000000 : ℝ)*base75 + (2211898022943851329/256500000000000000000000000000000 : ℝ)*base78 + (2129027266019351329/256500000000000000000000000000000 : ℝ)*base80 + (7843022786879/2565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3420587/1250000000000000000000 : ℝ)*base89 + (3420587/1250000000000000000000 : ℝ)*base91 + (3420587/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1554_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (991/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1554_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1554_s4_0 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-451919219/2500000000 : ℝ)*x 0 + (2714017129/5000000000 : ℝ)*x 1 + (5219298507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (451919219/2500000000 : ℝ)^4605 ≤ (11083879324649/100000000000000 : ℝ)^3581 := by
    have hnat : (451919219 : ℕ)^4605*100000000000000^3581 ≤ 11083879324649^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451919219 2500000000 11083879324649 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2714017129/5000000000 : ℝ)^4605 ≤ (22789388025423/50000000000000 : ℝ)^3581 := by
    have hnat : (2714017129 : ℕ)^4605*50000000000000^3581 ≤ 22789388025423^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714017129 5000000000 22789388025423 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219298507/10000000000 : ℝ)^4605 ≤ (2708584037623/6250000000000 : ℝ)^3581 := by
    have hnat : (5219298507 : ℕ)^4605*6250000000000^3581 ≤ 2708584037623^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219298507 10000000000 2708584037623 6250000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-451919219/2500000000 : ℝ), (2714017129/5000000000 : ℝ), (5219298507/10000000000 : ℝ)] ![(11083879324649/100000000000000 : ℝ), (22789388025423/50000000000000 : ℝ), (2708584037623/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-451919219/2500000000 : ℝ)|^4605 ≤ (11083879324649/100000000000000 : ℝ)^3581
        have hw : |(-451919219/2500000000 : ℝ)|=(451919219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2714017129/5000000000 : ℝ)|^4605 ≤ (22789388025423/50000000000000 : ℝ)^3581
        have hw : |(2714017129/5000000000 : ℝ)|=(2714017129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219298507/10000000000 : ℝ)|^4605 ≤ (2708584037623/6250000000000 : ℝ)^3581
        have hw : |(5219298507/10000000000 : ℝ)|=(5219298507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s4_1 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349216941/10000000000 : ℝ)*x 0 + (-957249471/5000000000 : ℝ)*x 1 + (2609649257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349216941/10000000000 : ℝ)^4605 ≤ (44729475651071/100000000000000 : ℝ)^3581 := by
    have hnat : (5349216941 : ℕ)^4605*100000000000000^3581 ≤ 44729475651071^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349216941 10000000000 44729475651071 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (957249471/5000000000 : ℝ)^4605 ≤ (2386635930611/20000000000000 : ℝ)^3581 := by
    have hnat : (957249471 : ℕ)^4605*20000000000000^3581 ≤ 2386635930611^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957249471 5000000000 2386635930611 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609649257/5000000000 : ℝ)^4605 ≤ (5417168084589/12500000000000 : ℝ)^3581 := by
    have hnat : (2609649257 : ℕ)^4605*12500000000000^3581 ≤ 5417168084589^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609649257 5000000000 5417168084589 12500000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349216941/10000000000 : ℝ), (-957249471/5000000000 : ℝ), (2609649257/5000000000 : ℝ)] ![(44729475651071/100000000000000 : ℝ), (2386635930611/20000000000000 : ℝ), (5417168084589/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349216941/10000000000 : ℝ)|^4605 ≤ (44729475651071/100000000000000 : ℝ)^3581
        have hw : |(5349216941/10000000000 : ℝ)|=(5349216941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-957249471/5000000000 : ℝ)|^4605 ≤ (2386635930611/20000000000000 : ℝ)^3581
        have hw : |(-957249471/5000000000 : ℝ)|=(957249471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609649257/5000000000 : ℝ)|^4605 ≤ (5417168084589/12500000000000 : ℝ)^3581
        have hw : |(2609649257/5000000000 : ℝ)|=(2609649257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s4_2 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674608471/5000000000 : ℝ)*x 0 + (1043859699/2000000000 : ℝ)*x 1 + (-957249483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674608471/5000000000 : ℝ)^4605 ≤ (2730070536/6103515625 : ℝ)^3581 := by
    have hnat : (2674608471 : ℕ)^4605*6103515625^3581 ≤ 2730070536^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674608471 5000000000 2730070536 6103515625 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043859699/2000000000 : ℝ)^4605 ≤ (10834336118459/25000000000000 : ℝ)^3581 := by
    have hnat : (1043859699 : ℕ)^4605*25000000000000^3581 ≤ 10834336118459^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043859699 2000000000 10834336118459 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957249483/5000000000 : ℝ)^4605 ≤ (477327193817/4000000000000 : ℝ)^3581 := by
    have hnat : (957249483 : ℕ)^4605*4000000000000^3581 ≤ 477327193817^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957249483 5000000000 477327193817 4000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674608471/5000000000 : ℝ), (1043859699/2000000000 : ℝ), (-957249483/5000000000 : ℝ)] ![(2730070536/6103515625 : ℝ), (10834336118459/25000000000000 : ℝ), (477327193817/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674608471/5000000000 : ℝ)|^4605 ≤ (2730070536/6103515625 : ℝ)^3581
        have hw : |(2674608471/5000000000 : ℝ)|=(2674608471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043859699/2000000000 : ℝ)|^4605 ≤ (10834336118459/25000000000000 : ℝ)^3581
        have hw : |(1043859699/2000000000 : ℝ)|=(1043859699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-957249483/5000000000 : ℝ)|^4605 ≤ (477327193817/4000000000000 : ℝ)^3581
        have hw : |(-957249483/5000000000 : ℝ)|=(957249483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s4_3 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062646511/2500000000 : ℝ)*x 0 + (2006316237/5000000000 : ℝ)*x 1 + (4500000093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062646511/2500000000 : ℝ)^4605 ≤ (4160182748497/12500000000000 : ℝ)^3581 := by
    have hnat : (1062646511 : ℕ)^4605*12500000000000^3581 ≤ 4160182748497^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062646511 2500000000 4160182748497 12500000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006316237/5000000000 : ℝ)^4605 ≤ (7726246844939/25000000000000 : ℝ)^3581 := by
    have hnat : (2006316237 : ℕ)^4605*25000000000000^3581 ≤ 7726246844939^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006316237 5000000000 7726246844939 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500000093/10000000000 : ℝ)^4605 ≤ (8953387654427/25000000000000 : ℝ)^3581 := by
    have hnat : (4500000093 : ℕ)^4605*25000000000000^3581 ≤ 8953387654427^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500000093 10000000000 8953387654427 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062646511/2500000000 : ℝ), (2006316237/5000000000 : ℝ), (4500000093/10000000000 : ℝ)] ![(4160182748497/12500000000000 : ℝ), (7726246844939/25000000000000 : ℝ), (8953387654427/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062646511/2500000000 : ℝ)|^4605 ≤ (4160182748497/12500000000000 : ℝ)^3581
        have hw : |(1062646511/2500000000 : ℝ)|=(1062646511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2006316237/5000000000 : ℝ)|^4605 ≤ (7726246844939/25000000000000 : ℝ)^3581
        have hw : |(2006316237/5000000000 : ℝ)|=(2006316237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500000093/10000000000 : ℝ)|^4605 ≤ (8953387654427/25000000000000 : ℝ)^3581
        have hw : |(4500000093/10000000000 : ℝ)|=(4500000093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s4_4 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-72308173/400000000 : ℝ)*x 0 + (5220384239/10000000000 : ℝ)*x 1 + (5426940527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72308173/400000000 : ℝ)^4605 ≤ (5542047878897/50000000000000 : ℝ)^3581 := by
    have hnat : (72308173 : ℕ)^4605*50000000000000^3581 ≤ 5542047878897^3581*400000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72308173 400000000 5542047878897 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220384239/10000000000 : ℝ)^4605 ≤ (21674469003769/50000000000000 : ℝ)^3581 := by
    have hnat : (5220384239 : ℕ)^4605*50000000000000^3581 ≤ 21674469003769^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220384239 10000000000 21674469003769 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426940527/10000000000 : ℝ)^4605 ≤ (18226786491/40000000000 : ℝ)^3581 := by
    have hnat : (5426940527 : ℕ)^4605*40000000000^3581 ≤ 18226786491^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426940527 10000000000 18226786491 40000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-72308173/400000000 : ℝ), (5220384239/10000000000 : ℝ), (5426940527/10000000000 : ℝ)] ![(5542047878897/50000000000000 : ℝ), (21674469003769/50000000000000 : ℝ), (18226786491/40000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-72308173/400000000 : ℝ)|^4605 ≤ (5542047878897/50000000000000 : ℝ)^3581
        have hw : |(-72308173/400000000 : ℝ)|=(72308173/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220384239/10000000000 : ℝ)|^4605 ≤ (21674469003769/50000000000000 : ℝ)^3581
        have hw : |(5220384239/10000000000 : ℝ)|=(5220384239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426940527/10000000000 : ℝ)|^4605 ≤ (18226786491/40000000000 : ℝ)^3581
        have hw : |(5426940527/10000000000 : ℝ)|=(5426940527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s4_5 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13235251/25000000 : ℝ)*x 0 + (-1706856951/10000000000 : ℝ)*x 1 + (1356735143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13235251/25000000 : ℝ)^4605 ≤ (44137683750111/100000000000000 : ℝ)^3581 := by
    have hnat : (13235251 : ℕ)^4605*100000000000000^3581 ≤ 44137683750111^3581*25000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13235251 25000000 44137683750111 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1706856951/10000000000 : ℝ)^4605 ≤ (10295349514537/100000000000000 : ℝ)^3581 := by
    have hnat : (1706856951 : ℕ)^4605*100000000000000^3581 ≤ 10295349514537^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1706856951 10000000000 10295349514537 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1356735143/2500000000 : ℝ)^4605 ≤ (9113393342677/20000000000000 : ℝ)^3581 := by
    have hnat : (1356735143 : ℕ)^4605*20000000000000^3581 ≤ 9113393342677^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356735143 2500000000 9113393342677 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13235251/25000000 : ℝ), (-1706856951/10000000000 : ℝ), (1356735143/2500000000 : ℝ)] ![(44137683750111/100000000000000 : ℝ), (10295349514537/100000000000000 : ℝ), (9113393342677/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13235251/25000000 : ℝ)|^4605 ≤ (44137683750111/100000000000000 : ℝ)^3581
        have hw : |(13235251/25000000 : ℝ)|=(13235251/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1706856951/10000000000 : ℝ)|^4605 ≤ (10295349514537/100000000000000 : ℝ)^3581
        have hw : |(-1706856951/10000000000 : ℝ)|=(1706856951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1356735143/2500000000 : ℝ)|^4605 ≤ (9113393342677/20000000000000 : ℝ)^3581
        have hw : |(1356735143/2500000000 : ℝ)|=(1356735143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s4_6 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82720319/156250000 : ℝ)*x 0 + (1356735149/2500000000 : ℝ)*x 1 + (-341371379/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82720319/156250000 : ℝ)^4605 ≤ (882753678433/2000000000000 : ℝ)^3581 := by
    have hnat : (82720319 : ℕ)^4605*2000000000000^3581 ≤ 882753678433^3581*156250000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82720319 156250000 882753678433 2000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356735149/2500000000 : ℝ)^4605 ≤ (45566966972523/100000000000000 : ℝ)^3581 := by
    have hnat : (1356735149 : ℕ)^4605*100000000000000^3581 ≤ 45566966972523^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356735149 2500000000 45566966972523 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341371379/2000000000 : ℝ)^4605 ≤ (1029534908017/10000000000000 : ℝ)^3581 := by
    have hnat : (341371379 : ℕ)^4605*10000000000000^3581 ≤ 1029534908017^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341371379 2000000000 1029534908017 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82720319/156250000 : ℝ), (1356735149/2500000000 : ℝ), (-341371379/2000000000 : ℝ)] ![(882753678433/2000000000000 : ℝ), (45566966972523/100000000000000 : ℝ), (1029534908017/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82720319/156250000 : ℝ)|^4605 ≤ (882753678433/2000000000000 : ℝ)^3581
        have hw : |(82720319/156250000 : ℝ)|=(82720319/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356735149/2500000000 : ℝ)|^4605 ≤ (45566966972523/100000000000000 : ℝ)^3581
        have hw : |(1356735149/2500000000 : ℝ)|=(1356735149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341371379/2000000000 : ℝ)|^4605 ≤ (1029534908017/10000000000000 : ℝ)^3581
        have hw : |(-341371379/2000000000 : ℝ)|=(341371379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s4_7 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062662573/2500000000 : ℝ)*x 0 + (2248732549/5000000000 : ℝ)*x 1 + (4015186181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062662573/2500000000 : ℝ)^4605 ≤ (16641054445699/50000000000000 : ℝ)^3581 := by
    have hnat : (1062662573 : ℕ)^4605*50000000000000^3581 ≤ 16641054445699^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062662573 2500000000 16641054445699 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2248732549/5000000000 : ℝ)^4605 ≤ (35787608687177/100000000000000 : ℝ)^3581 := by
    have hnat : (2248732549 : ℕ)^4605*100000000000000^3581 ≤ 35787608687177^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248732549 5000000000 35787608687177 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4015186181/10000000000 : ℝ)^4605 ≤ (7732570600671/25000000000000 : ℝ)^3581 := by
    have hnat : (4015186181 : ℕ)^4605*25000000000000^3581 ≤ 7732570600671^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4015186181 10000000000 7732570600671 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062662573/2500000000 : ℝ), (2248732549/5000000000 : ℝ), (4015186181/10000000000 : ℝ)] ![(16641054445699/50000000000000 : ℝ), (35787608687177/100000000000000 : ℝ), (7732570600671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062662573/2500000000 : ℝ)|^4605 ≤ (16641054445699/50000000000000 : ℝ)^3581
        have hw : |(1062662573/2500000000 : ℝ)|=(1062662573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2248732549/5000000000 : ℝ)|^4605 ≤ (35787608687177/100000000000000 : ℝ)^3581
        have hw : |(2248732549/5000000000 : ℝ)|=(2248732549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4015186181/10000000000 : ℝ)|^4605 ≤ (7732570600671/25000000000000 : ℝ)^3581
        have hw : |(4015186181/10000000000 : ℝ)|=(4015186181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1554_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1383/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15527/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15527/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15527/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15527/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15527/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15527/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11029/100000 : ℝ) ^ (4603/1024 : ℝ) ≤ (1241731620327959/25000000000000000000 : ℝ) := by
    have hpowers : (11029/100000 : ℝ)^4603 ≤ (1241731620327959/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11029 : ℕ)^4603*25000000000000000000^1024 ≤ 1241731620327959^1024*100000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11029 100000 1241731620327959 25000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11029/100000 : ℝ)) (X := (1241731620327959/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15527/100000 : ℝ) ^ (4603/1024 : ℝ) ≤ (23112331412973069/100000000000000000000 : ℝ) := by
    have hpowers : (15527/100000 : ℝ)^4603 ≤ (23112331412973069/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15527 : ℕ)^4603*100000000000000000000^1024 ≤ 23112331412973069^1024*100000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15527 100000 23112331412973069 100000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15527/100000 : ℝ)) (X := (23112331412973069/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501241731620327959/12500000000000000000 : ℝ) ≤ (400008839341827/400000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (12501241731620327959/12500000000000000000 : ℝ)^1024 ≤ (400008839341827/400000000000000 : ℝ)^4603 := by
      have hnat : (12501241731620327959 : ℕ)^1024*400000000000000^4603 ≤ 400008839341827^4603*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501241731620327959 12500000000000000000 400008839341827 400000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400008839341827/400000000000000 : ℝ)) (X := (12501241731620327959/12500000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005615851578856981/20000000000000000000 : ℝ) ≤ (10000624593130963/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (20005615851578856981/20000000000000000000 : ℝ)^1024 ≤ (10000624593130963/10000000000000000 : ℝ)^4603 := by
      have hnat : (20005615851578856981 : ℕ)^1024*10000000000000000^4603 ≤ 10000624593130963^4603*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005615851578856981 20000000000000000000 10000624593130963 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000624593130963/10000000000000000 : ℝ)) (X := (20005615851578856981/20000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023112331412973069/50000000000000000000 : ℝ) ≤ (10001028202716251/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (50023112331412973069/50000000000000000000 : ℝ)^1024 ≤ (10001028202716251/10000000000000000 : ℝ)^4603 := by
      have hnat : (50023112331412973069 : ℕ)^1024*10000000000000000^4603 ≤ 10001028202716251^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023112331412973069 50000000000000000000 10001028202716251 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001028202716251/10000000000000000 : ℝ)) (X := (50023112331412973069/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1241731620327959/25000000000000000000 : ℝ) ≤ ((1729695813990621671/1730000000000000000 : ℝ)+2*(3880861397/4325000000000 : ℝ)*(11029/100000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (1729695813990621671/1730000000000000000 : ℝ)+2*(3880861397/4325000000000 : ℝ)*(11029/100000 : ℝ)=(400008839341827/400000000000000 : ℝ) by norm_num, show 1+2*(1241731620327959/25000000000000000000 : ℝ)=(12501241731620327959/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23112331412973069/100000000000000000000 : ℝ)+(1241731620327959/25000000000000000000 : ℝ) ≤ ((1729695813990621671/1730000000000000000 : ℝ)+(3880861397/4325000000000 : ℝ)*((15527/100000 : ℝ)+(11029/100000 : ℝ)))^(4603/1024 : ℝ) := by
    rw [show (1729695813990621671/1730000000000000000 : ℝ)+(3880861397/4325000000000 : ℝ)*((15527/100000 : ℝ)+(11029/100000 : ℝ))=(10000624593130963/10000000000000000 : ℝ) by norm_num, show 1+(23112331412973069/100000000000000000000 : ℝ)+(1241731620327959/25000000000000000000 : ℝ)=(20005615851578856981/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23112331412973069/100000000000000000000 : ℝ) ≤ ((1729695813990621671/1730000000000000000 : ℝ)+2*(3880861397/4325000000000 : ℝ)*(15527/100000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (1729695813990621671/1730000000000000000 : ℝ)+2*(3880861397/4325000000000 : ℝ)*(15527/100000 : ℝ)=(10001028202716251/10000000000000000 : ℝ) by norm_num, show 1+2*(23112331412973069/100000000000000000000 : ℝ)=(50023112331412973069/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1729695813990621671/1730000000000000000 : ℝ)*(X 1 0+X 2 0)+(3880861397/4325000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (1729695813990621671/1730000000000000000 : ℝ)) (alpha := (3880861397/4325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1729695813990621671/1730000000000000000 : ℝ)*(X 0 1+X 2 1)+(3880861397/4325000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (1729695813990621671/1730000000000000000 : ℝ)) (alpha := (3880861397/4325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1729695813990621671/1730000000000000000 : ℝ)*(X 0 2+X 1 2)+(3880861397/4325000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (15527/100000 : ℝ)) (c := (1729695813990621671/1730000000000000000 : ℝ)) (alpha := (3880861397/4325000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-451919219/2500000000 : ℝ)*X 0 0+(2714017129/5000000000 : ℝ)*X 0 1+(5219298507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349216941/10000000000 : ℝ)*X 1 0+(-957249471/5000000000 : ℝ)*X 1 1+(2609649257/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674608471/5000000000 : ℝ)*X 2 0+(1043859699/2000000000 : ℝ)*X 2 1+(-957249483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062646511/2500000000 : ℝ)*X 0 0+(2006316237/5000000000 : ℝ)*X 0 1+(4500000093/10000000000 : ℝ)*X 0 2+(1062646511/2500000000 : ℝ)*X 1 0+(2006316237/5000000000 : ℝ)*X 1 1+(4500000093/10000000000 : ℝ)*X 1 2+(1062646511/2500000000 : ℝ)*X 2 0+(2006316237/5000000000 : ℝ)*X 2 1+(4500000093/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-72308173/400000000 : ℝ)*X 0 0+(5220384239/10000000000 : ℝ)*X 0 1+(5426940527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((13235251/25000000 : ℝ)*X 1 0+(-1706856951/10000000000 : ℝ)*X 1 1+(1356735143/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82720319/156250000 : ℝ)*X 2 0+(1356735149/2500000000 : ℝ)*X 2 1+(-341371379/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1062662573/2500000000 : ℝ)*X 0 0+(2248732549/5000000000 : ℝ)*X 0 1+(4015186181/10000000000 : ℝ)*X 0 2+(1062662573/2500000000 : ℝ)*X 1 0+(2248732549/5000000000 : ℝ)*X 1 1+(4015186181/10000000000 : ℝ)*X 1 2+(1062662573/2500000000 : ℝ)*X 2 0+(2248732549/5000000000 : ℝ)*X 2 1+(4015186181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (794389299945020371791918969/86500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1541067811/100000000000000 : ℝ)*(base19) + (366033687/25000000000000 : ℝ)*(base23) + (41632243/100000000000000 : ℝ)*(lower2) + (23034441/10000000000000 : ℝ)*(upper3) + (30083413/20000000000000 : ℝ)*(upper5) + (3421329067982613/100000000000000 : ℝ)*(major0) + (3421329067982613/100000000000000 : ℝ)*(major1) + (3421329067982613/100000000000000 : ℝ)*(major2) + (4790772095753621/100000000000000 : ℝ)*(sp0) + (598849388004493/12500000000000 : ℝ)*(sp1) + (2395397590484503/50000000000000 : ℝ)*(sp2) + (512962398961191/25000000000000 : ℝ)*(sp3) + (24549350133/100000000000000 : ℝ)*(sp4) + (11588893653/100000000000000 : ℝ)*(sp7) + (128241324046151/6250000000000 : ℝ)*(f.failure) + (958159329020751/20000000000000 : ℝ)*(f.sum) + (7939638104971/865000000000000000000000000 : ℝ)*base66 + (1050193232521593677/173000000000000000000000000000000 : ℝ)*base68 + (195672314174406323/173000000000000000000000000000000 : ℝ)*base69 + (1160654850274593677/173000000000000000000000000000000 : ℝ)*base72 + (1842196203243/432500000000000000000000000 : ℝ)*base74 + (583883552919593677/173000000000000000000000000000000 : ℝ)*base76 + (1810161266478593677/173000000000000000000000000000000 : ℝ)*base78 + (241053861533406323/173000000000000000000000000000000 : ℝ)*base79 + (1003728913059/865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1040971/156250000000000000000 : ℝ)*base90 + (1040971/156250000000000000000 : ℝ)*base92 + (1040971/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (104594948208126273631721691/21625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (301052107/50000000000000 : ℝ)*(base19) + (740383573/100000000000000 : ℝ)*(base23) + (50106137/50000000000000 : ℝ)*(upper3) + (48170431/100000000000000 : ℝ)*(lower4) + (88352387/100000000000000 : ℝ)*(upper5) + (864347921128207/25000000000000 : ℝ)*(major0) + (864347921128207/25000000000000 : ℝ)*(major1) + (864347921128207/25000000000000 : ℝ)*(major2) + (9483598183/100000000000000 : ℝ)*(sp1) + (12620587471/100000000000000 : ℝ)*(sp2) + (4841294321777337/100000000000000 : ℝ)*(sp4) + (4841284236074939/100000000000000 : ℝ)*(sp5) + (1210320240201573/25000000000000 : ℝ)*(sp6) + (25918611075287/1250000000000 : ℝ)*(sp7) + (25918611075287/1250000000000 : ℝ)*(f.failure) + (4841294321777337/100000000000000 : ℝ)*(f.sum) + (1978135150189/865000000000000000000000000 : ℝ)*base65 + (71236708499576103/43250000000000000000000000000000 : ℝ)*base68 + (54027997831576103/43250000000000000000000000000000 : ℝ)*base70 + (298812172875423897/43250000000000000000000000000000 : ℝ)*base71 + (1888548846961/865000000000000000000000000 : ℝ)*base74 + (381045078527326103/43250000000000000000000000000000 : ℝ)*base76 + (21392444673897/43250000000000000000000000000000 : ℝ)*base77 + (63062226420076103/43250000000000000000000000000000 : ℝ)*base80 + (1257972011227/432500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (35127/31250000000000000000 : ℝ)*base90 + (35127/31250000000000000000 : ℝ)*base92 + (35127/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1554_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15527/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1554_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1554_s5_0 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1807706141/10000000000 : ℝ)*x 0 + (2713919989/5000000000 : ℝ)*x 1 + (2609736683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1807706141/10000000000 : ℝ)^4605 ≤ (277102751921/2500000000000 : ℝ)^3581 := by
    have hnat : (1807706141 : ℕ)^4605*2500000000000^3581 ≤ 277102751921^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1807706141 10000000000 277102751921 2500000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713919989/5000000000 : ℝ)^4605 ≤ (22788339108073/50000000000000 : ℝ)^3581 := by
    have hnat : (2713919989 : ℕ)^4605*50000000000000^3581 ≤ 22788339108073^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713919989 5000000000 22788339108073 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609736683/5000000000 : ℝ)^4605 ≤ (21669605846613/50000000000000 : ℝ)^3581 := by
    have hnat : (2609736683 : ℕ)^4605*50000000000000^3581 ≤ 21669605846613^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609736683 5000000000 21669605846613 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1807706141/10000000000 : ℝ), (2713919989/5000000000 : ℝ), (2609736683/5000000000 : ℝ)] ![(277102751921/2500000000000 : ℝ), (22788339108073/50000000000000 : ℝ), (21669605846613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1807706141/10000000000 : ℝ)|^4605 ≤ (277102751921/2500000000000 : ℝ)^3581
        have hw : |(-1807706141/10000000000 : ℝ)|=(1807706141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713919989/5000000000 : ℝ)|^4605 ≤ (22788339108073/50000000000000 : ℝ)^3581
        have hw : |(2713919989/5000000000 : ℝ)|=(2713919989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609736683/5000000000 : ℝ)|^4605 ≤ (21669605846613/50000000000000 : ℝ)^3581
        have hw : |(2609736683/5000000000 : ℝ)|=(2609736683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s5_1 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337291383/2500000000 : ℝ)*x 0 + (-239291873/1250000000 : ℝ)*x 1 + (5219473363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337291383/2500000000 : ℝ)^4605 ≤ (44728922851791/100000000000000 : ℝ)^3581 := by
    have hnat : (1337291383 : ℕ)^4605*100000000000000^3581 ≤ 44728922851791^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337291383 2500000000 44728922851791 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (239291873/1250000000 : ℝ)^4605 ≤ (11931865476679/100000000000000 : ℝ)^3581 := by
    have hnat : (239291873 : ℕ)^4605*100000000000000^3581 ≤ 11931865476679^3581*1250000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239291873 1250000000 11931865476679 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219473363/10000000000 : ℝ)^4605 ≤ (43339211661193/100000000000000 : ℝ)^3581 := by
    have hnat : (5219473363 : ℕ)^4605*100000000000000^3581 ≤ 43339211661193^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219473363 10000000000 43339211661193 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337291383/2500000000 : ℝ), (-239291873/1250000000 : ℝ), (5219473363/10000000000 : ℝ)] ![(44728922851791/100000000000000 : ℝ), (11931865476679/100000000000000 : ℝ), (43339211661193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337291383/2500000000 : ℝ)|^4605 ≤ (44728922851791/100000000000000 : ℝ)^3581
        have hw : |(1337291383/2500000000 : ℝ)|=(1337291383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-239291873/1250000000 : ℝ)|^4605 ≤ (11931865476679/100000000000000 : ℝ)^3581
        have hw : |(-239291873/1250000000 : ℝ)|=(239291873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219473363/10000000000 : ℝ)|^4605 ≤ (43339211661193/100000000000000 : ℝ)^3581
        have hw : |(5219473363/10000000000 : ℝ)|=(5219473363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s5_2 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534916553/1000000000 : ℝ)*x 0 + (1304868341/2500000000 : ℝ)*x 1 + (-382866997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534916553/1000000000 : ℝ)^4605 ≤ (8945784566057/20000000000000 : ℝ)^3581 := by
    have hnat : (534916553 : ℕ)^4605*20000000000000^3581 ≤ 8945784566057^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534916553 1000000000 8945784566057 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304868341/2500000000 : ℝ)^4605 ≤ (4333921167187/10000000000000 : ℝ)^3581 := by
    have hnat : (1304868341 : ℕ)^4605*10000000000000^3581 ≤ 4333921167187^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304868341 2500000000 4333921167187 10000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382866997/2000000000 : ℝ)^4605 ≤ (5965932742347/50000000000000 : ℝ)^3581 := by
    have hnat : (382866997 : ℕ)^4605*50000000000000^3581 ≤ 5965932742347^3581*2000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382866997 2000000000 5965932742347 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534916553/1000000000 : ℝ), (1304868341/2500000000 : ℝ), (-382866997/2000000000 : ℝ)] ![(8945784566057/20000000000000 : ℝ), (4333921167187/10000000000000 : ℝ), (5965932742347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534916553/1000000000 : ℝ)|^4605 ≤ (8945784566057/20000000000000 : ℝ)^3581
        have hw : |(534916553/1000000000 : ℝ)|=(534916553/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304868341/2500000000 : ℝ)|^4605 ≤ (4333921167187/10000000000000 : ℝ)^3581
        have hw : |(1304868341/2500000000 : ℝ)|=(1304868341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382866997/2000000000 : ℝ)|^4605 ≤ (5965932742347/50000000000000 : ℝ)^3581
        have hw : |(-382866997/2000000000 : ℝ)|=(382866997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s5_3 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2125302133/5000000000 : ℝ)*x 0 + (2006530689/5000000000 : ℝ)*x 1 + (112489177/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2125302133/5000000000 : ℝ)^4605 ≤ (33281645462261/100000000000000 : ℝ)^3581 := by
    have hnat : (2125302133 : ℕ)^4605*100000000000000^3581 ≤ 33281645462261^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125302133 5000000000 33281645462261 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2006530689/5000000000 : ℝ)^4605 ≤ (6181847089109/20000000000000 : ℝ)^3581 := by
    have hnat : (2006530689 : ℕ)^4605*20000000000000^3581 ≤ 6181847089109^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2006530689 5000000000 6181847089109 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112489177/250000000 : ℝ)^4605 ≤ (35809119073047/100000000000000 : ℝ)^3581 := by
    have hnat : (112489177 : ℕ)^4605*100000000000000^3581 ≤ 35809119073047^3581*250000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112489177 250000000 35809119073047 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2125302133/5000000000 : ℝ), (2006530689/5000000000 : ℝ), (112489177/250000000 : ℝ)] ![(33281645462261/100000000000000 : ℝ), (6181847089109/20000000000000 : ℝ), (35809119073047/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2125302133/5000000000 : ℝ)|^4605 ≤ (33281645462261/100000000000000 : ℝ)^3581
        have hw : |(2125302133/5000000000 : ℝ)|=(2125302133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2006530689/5000000000 : ℝ)|^4605 ≤ (6181847089109/20000000000000 : ℝ)^3581
        have hw : |(2006530689/5000000000 : ℝ)|=(2006530689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112489177/250000000 : ℝ)|^4605 ≤ (35809119073047/100000000000000 : ℝ)^3581
        have hw : |(112489177/250000000 : ℝ)|=(112489177/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s5_4 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-180773351/1000000000 : ℝ)*x 0 + (1305138807/2500000000 : ℝ)*x 1 + (542675011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (180773351/1000000000 : ℝ)^4605 ≤ (11084325880189/100000000000000 : ℝ)^3581 := by
    have hnat : (180773351 : ℕ)^4605*100000000000000^3581 ≤ 11084325880189^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180773351 1000000000 11084325880189 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305138807/2500000000 : ℝ)^4605 ≤ (21675381942257/50000000000000 : ℝ)^3581 := by
    have hnat : (1305138807 : ℕ)^4605*50000000000000^3581 ≤ 21675381942257^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305138807 2500000000 21675381942257 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542675011/1000000000 : ℝ)^4605 ≤ (45564910223733/100000000000000 : ℝ)^3581 := by
    have hnat : (542675011 : ℕ)^4605*100000000000000^3581 ≤ 45564910223733^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542675011 1000000000 45564910223733 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-180773351/1000000000 : ℝ), (1305138807/2500000000 : ℝ), (542675011/1000000000 : ℝ)] ![(11084325880189/100000000000000 : ℝ), (21675381942257/50000000000000 : ℝ), (45564910223733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-180773351/1000000000 : ℝ)|^4605 ≤ (11084325880189/100000000000000 : ℝ)^3581
        have hw : |(-180773351/1000000000 : ℝ)|=(180773351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305138807/2500000000 : ℝ)|^4605 ≤ (21675381942257/50000000000000 : ℝ)^3581
        have hw : |(1305138807/2500000000 : ℝ)|=(1305138807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542675011/1000000000 : ℝ)|^4605 ≤ (45564910223733/100000000000000 : ℝ)^3581
        have hw : |(542675011/1000000000 : ℝ)|=(542675011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s5_5 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294146569/10000000000 : ℝ)*x 0 + (-1707058259/10000000000 : ℝ)*x 1 + (169585941/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294146569/10000000000 : ℝ)^4605 ≤ (1379318085531/3125000000000 : ℝ)^3581 := by
    have hnat : (5294146569 : ℕ)^4605*3125000000000^3581 ≤ 1379318085531^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294146569 10000000000 1379318085531 3125000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1707058259/10000000000 : ℝ)^4605 ≤ (2059382199781/20000000000000 : ℝ)^3581 := by
    have hnat : (1707058259 : ℕ)^4605*20000000000000^3581 ≤ 2059382199781^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1707058259 10000000000 2059382199781 20000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169585941/312500000 : ℝ)^4605 ≤ (2847806890333/6250000000000 : ℝ)^3581 := by
    have hnat : (169585941 : ℕ)^4605*6250000000000^3581 ≤ 2847806890333^3581*312500000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169585941 312500000 2847806890333 6250000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294146569/10000000000 : ℝ), (-1707058259/10000000000 : ℝ), (169585941/312500000 : ℝ)] ![(1379318085531/3125000000000 : ℝ), (2059382199781/20000000000000 : ℝ), (2847806890333/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294146569/10000000000 : ℝ)|^4605 ≤ (1379318085531/3125000000000 : ℝ)^3581
        have hw : |(5294146569/10000000000 : ℝ)|=(5294146569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1707058259/10000000000 : ℝ)|^4605 ≤ (2059382199781/20000000000000 : ℝ)^3581
        have hw : |(-1707058259/10000000000 : ℝ)|=(1707058259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169585941/312500000 : ℝ)|^4605 ≤ (2847806890333/6250000000000 : ℝ)^3581
        have hw : |(169585941/312500000 : ℝ)|=(169585941/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s5_6 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294146573/10000000000 : ℝ)*x 0 + (542675011/1000000000 : ℝ)*x 1 + (-853529129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294146573/10000000000 : ℝ)^4605 ≤ (44138178779877/100000000000000 : ℝ)^3581 := by
    have hnat : (5294146573 : ℕ)^4605*100000000000000^3581 ≤ 44138178779877^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294146573 10000000000 44138178779877 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542675011/1000000000 : ℝ)^4605 ≤ (45564910223733/100000000000000 : ℝ)^3581 := by
    have hnat : (542675011 : ℕ)^4605*100000000000000^3581 ≤ 45564910223733^3581*1000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542675011 1000000000 45564910223733 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (853529129/5000000000 : ℝ)^4605 ≤ (2574227747787/25000000000000 : ℝ)^3581 := by
    have hnat : (853529129 : ℕ)^4605*25000000000000^3581 ≤ 2574227747787^3581*5000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853529129 5000000000 2574227747787 25000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294146573/10000000000 : ℝ), (542675011/1000000000 : ℝ), (-853529129/5000000000 : ℝ)] ![(44138178779877/100000000000000 : ℝ), (45564910223733/100000000000000 : ℝ), (2574227747787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294146573/10000000000 : ℝ)|^4605 ≤ (44138178779877/100000000000000 : ℝ)^3581
        have hw : |(5294146573/10000000000 : ℝ)|=(5294146573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542675011/1000000000 : ℝ)|^4605 ≤ (45564910223733/100000000000000 : ℝ)^3581
        have hw : |(542675011/1000000000 : ℝ)|=(542675011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-853529129/5000000000 : ℝ)|^4605 ≤ (2574227747787/25000000000000 : ℝ)^3581
        have hw : |(-853529129/5000000000 : ℝ)|=(853529129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1554_s5_7 (p : ℝ) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (85013363/200000000 : ℝ)*x 0 + (4497041067/10000000000 : ℝ)*x 1 + (1003901507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85013363/200000000 : ℝ)^4605 ≤ (33282288701403/100000000000000 : ℝ)^3581 := by
    have hnat : (85013363 : ℕ)^4605*100000000000000^3581 ≤ 33282288701403^3581*200000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85013363 200000000 33282288701403 100000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497041067/10000000000 : ℝ)^4605 ≤ (17891634882077/50000000000000 : ℝ)^3581 := by
    have hnat : (4497041067 : ℕ)^4605*50000000000000^3581 ≤ 17891634882077^3581*10000000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497041067 10000000000 17891634882077 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1003901507/2500000000 : ℝ)^4605 ≤ (15467220759459/50000000000000 : ℝ)^3581 := by
    have hnat : (1003901507 : ℕ)^4605*50000000000000^3581 ≤ 15467220759459^3581*2500000000^4605 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003901507 2500000000 15467220759459 50000000000000 4605 3581 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4605/1024 : ℝ)) 4605 3581 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(85013363/200000000 : ℝ), (4497041067/10000000000 : ℝ), (1003901507/2500000000 : ℝ)] ![(33282288701403/100000000000000 : ℝ), (17891634882077/50000000000000 : ℝ), (15467220759459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(85013363/200000000 : ℝ)|^4605 ≤ (33282288701403/100000000000000 : ℝ)^3581
        have hw : |(85013363/200000000 : ℝ)|=(85013363/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497041067/10000000000 : ℝ)|^4605 ≤ (17891634882077/50000000000000 : ℝ)^3581
        have hw : |(4497041067/10000000000 : ℝ)|=(4497041067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1003901507/2500000000 : ℝ)|^4605 ≤ (15467220759459/50000000000000 : ℝ)^3581
        have hw : |(1003901507/2500000000 : ℝ)|=(1003901507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1554_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2767/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1383/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1383/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1383/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1383/12500 : ℝ) ^ (4603/1024 : ℝ) ≤ (2519086925882377/50000000000000000000 : ℝ) := by
    have hpowers : (1383/12500 : ℝ)^4603 ≤ (2519086925882377/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1383 : ℕ)^4603*50000000000000000000^1024 ≤ 2519086925882377^1024*12500^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1383 12500 2519086925882377 50000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1383/12500 : ℝ)) (X := (2519086925882377/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4603/1024 : ℝ) ≤ (22859155024837007/100000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4603 ≤ (22859155024837007/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4603*100000000000000000000^1024 ≤ 22859155024837007^1024*100000^4603 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 22859155024837007 100000000000000000000 4603 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (22859155024837007/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002519086925882377/25000000000000000000 : ℝ) ≤ (200004483065771/200000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (25002519086925882377/25000000000000000000 : ℝ)^1024 ≤ (200004483065771/200000000000000 : ℝ)^4603 := by
      have hnat : (25002519086925882377 : ℕ)^1024*200000000000000^4603 ≤ 200004483065771^4603*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002519086925882377 25000000000000000000 200004483065771 200000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200004483065771/200000000000000 : ℝ)) (X := (25002519086925882377/25000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100027897328876601761/100000000000000000000 : ℝ) ≤ (10000620546752889/10000000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (100027897328876601761/100000000000000000000 : ℝ)^1024 ≤ (10000620546752889/10000000000000000 : ℝ)^4603 := by
      have hnat : (100027897328876601761 : ℕ)^1024*10000000000000000^4603 ≤ 10000620546752889^4603*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100027897328876601761 100000000000000000000 10000620546752889 10000000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000620546752889/10000000000000000 : ℝ)) (X := (100027897328876601761/100000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022859155024837007/50000000000000000000 : ℝ) ≤ (2500254235054307/2500000000000000 : ℝ) ^ (4603/1024 : ℝ) := by
    have hpowers : (50022859155024837007/50000000000000000000 : ℝ)^1024 ≤ (2500254235054307/2500000000000000 : ℝ)^4603 := by
      have hnat : (50022859155024837007 : ℕ)^1024*2500000000000000^4603 ≤ 2500254235054307^4603*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022859155024837007 50000000000000000000 2500254235054307 2500000000000000 1024 4603 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500254235054307/2500000000000000 : ℝ)) (X := (50022859155024837007/50000000000000000000 : ℝ)) (by norm_num) 4603 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2519086925882377/50000000000000000000 : ℝ) ≤ ((7373703413953823393/7375000000000000000 : ℝ)+2*(396393464339/442500000000000 : ℝ)*(1383/12500 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (7373703413953823393/7375000000000000000 : ℝ)+2*(396393464339/442500000000000 : ℝ)*(1383/12500 : ℝ)=(200004483065771/200000000000000 : ℝ) by norm_num, show 1+2*(2519086925882377/50000000000000000000 : ℝ)=(25002519086925882377/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22859155024837007/100000000000000000000 : ℝ)+(2519086925882377/50000000000000000000 : ℝ) ≤ ((7373703413953823393/7375000000000000000 : ℝ)+(396393464339/442500000000000 : ℝ)*((15489/100000 : ℝ)+(1383/12500 : ℝ)))^(4603/1024 : ℝ) := by
    rw [show (7373703413953823393/7375000000000000000 : ℝ)+(396393464339/442500000000000 : ℝ)*((15489/100000 : ℝ)+(1383/12500 : ℝ))=(10000620546752889/10000000000000000 : ℝ) by norm_num, show 1+(22859155024837007/100000000000000000000 : ℝ)+(2519086925882377/50000000000000000000 : ℝ)=(100027897328876601761/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22859155024837007/100000000000000000000 : ℝ) ≤ ((7373703413953823393/7375000000000000000 : ℝ)+2*(396393464339/442500000000000 : ℝ)*(15489/100000 : ℝ))^(4603/1024 : ℝ) := by
    rw [show (7373703413953823393/7375000000000000000 : ℝ)+2*(396393464339/442500000000000 : ℝ)*(15489/100000 : ℝ)=(2500254235054307/2500000000000000 : ℝ) by norm_num, show 1+2*(22859155024837007/100000000000000000000 : ℝ)=(50022859155024837007/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7373703413953823393/7375000000000000000 : ℝ)*(X 1 0+X 2 0)+(396393464339/442500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (7373703413953823393/7375000000000000000 : ℝ)) (alpha := (396393464339/442500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7373703413953823393/7375000000000000000 : ℝ)*(X 0 1+X 2 1)+(396393464339/442500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (7373703413953823393/7375000000000000000 : ℝ)) (alpha := (396393464339/442500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7373703413953823393/7375000000000000000 : ℝ)*(X 0 2+X 1 2)+(396393464339/442500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4603/1024 : ℝ)) (lo := (1383/12500 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (7373703413953823393/7375000000000000000 : ℝ)) (alpha := (396393464339/442500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1807706141/10000000000 : ℝ)*X 0 0+(2713919989/5000000000 : ℝ)*X 0 1+(2609736683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337291383/2500000000 : ℝ)*X 1 0+(-239291873/1250000000 : ℝ)*X 1 1+(5219473363/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534916553/1000000000 : ℝ)*X 2 0+(1304868341/2500000000 : ℝ)*X 2 1+(-382866997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2125302133/5000000000 : ℝ)*X 0 0+(2006530689/5000000000 : ℝ)*X 0 1+(112489177/250000000 : ℝ)*X 0 2+(2125302133/5000000000 : ℝ)*X 1 0+(2006530689/5000000000 : ℝ)*X 1 1+(112489177/250000000 : ℝ)*X 1 2+(2125302133/5000000000 : ℝ)*X 2 0+(2006530689/5000000000 : ℝ)*X 2 1+(112489177/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-180773351/1000000000 : ℝ)*X 0 0+(1305138807/2500000000 : ℝ)*X 0 1+(542675011/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294146569/10000000000 : ℝ)*X 1 0+(-1707058259/10000000000 : ℝ)*X 1 1+(169585941/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294146573/10000000000 : ℝ)*X 2 0+(542675011/1000000000 : ℝ)*X 2 1+(-853529129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((85013363/200000000 : ℝ)*X 0 0+(4497041067/10000000000 : ℝ)*X 0 1+(1003901507/2500000000 : ℝ)*X 0 2+(85013363/200000000 : ℝ)*X 1 0+(4497041067/10000000000 : ℝ)*X 1 1+(1003901507/2500000000 : ℝ)*X 1 2+(85013363/200000000 : ℝ)*X 2 0+(4497041067/10000000000 : ℝ)*X 2 1+(1003901507/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1554_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1201569873539003186141178927/184375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27870269/2500000000000 : ℝ)*(base19) + (519729489/50000000000000 : ℝ)*(base23) + (19673531/50000000000000 : ℝ)*(lower2) + (81223013/50000000000000 : ℝ)*(upper3) + (10790447/10000000000000 : ℝ)*(upper5) + (1713690008280413/50000000000000 : ℝ)*(major0) + (1713690008280413/50000000000000 : ℝ)*(major1) + (1713690008280413/50000000000000 : ℝ)*(major2) + (191970076521807/4000000000000 : ℝ)*(sp0) + (4799268603051187/100000000000000 : ℝ)*(sp1) + (4799268678402969/100000000000000 : ℝ)*(sp2) + (102774089097871/5000000000000 : ℝ)*(sp3) + (17804816771/100000000000000 : ℝ)*(sp4) + (4158034653/50000000000000 : ℝ)*(sp7) + (1027745049013363/50000000000000 : ℝ)*(f.failure) + (4799269717861947/100000000000000 : ℝ)*(f.sum) + (10964969497139/22125000000000000000000000000 : ℝ)*base65 + (368964671030346073/1106250000000000000000000000000000 : ℝ)*base68 + (7383342362994653927/1106250000000000000000000000000000 : ℝ)*base69 + (1189796533580346073/1106250000000000000000000000000000 : ℝ)*base72 + (3721852779467/2765625000000000000000000000 : ℝ)*base74 + (16567664885236596073/1106250000000000000000000000000000 : ℝ)*base76 + (1363016846282153927/1106250000000000000000000000000000 : ℝ)*base77 + (1190778744192846073/1106250000000000000000000000000000 : ℝ)*base80 + (106899014455139/22125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (8271523/1250000000000000000000 : ℝ)*base90 + (8271523/1250000000000000000000 : ℝ)*base92 + (8271523/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (962939955941289507350199431/184375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411765011/50000000000000 : ℝ)*(base19) + (890249471/100000000000000 : ℝ)*(base23) + (259209097/100000000000000 : ℝ)*(lower1) + (118381721/100000000000000 : ℝ)*(upper3) + (5535171/20000000000000 : ℝ)*(lower4) + (22577777/20000000000000 : ℝ)*(upper5) + (1731721451408411/50000000000000 : ℝ)*(major0) + (1731721451408411/50000000000000 : ℝ)*(major1) + (1731721451408411/50000000000000 : ℝ)*(major2) + (1037185409/100000000000000 : ℝ)*(sp2) + (2424883835234927/50000000000000 : ℝ)*(sp4) + (606220855867479/12500000000000 : ℝ)*(sp5) + (193990629721399/4000000000000 : ℝ)*(sp6) + (2077117961072927/100000000000000 : ℝ)*(sp7) + (2077117961072927/100000000000000 : ℝ)*(f.failure) + (2424883835234927/50000000000000 : ℝ)*(f.sum) + (16690393712023/5531250000000000000000000000 : ℝ)*base66 + (3807136712088524431/1106250000000000000000000000000000 : ℝ)*base68 + (17222235417442725569/1106250000000000000000000000000000 : ℝ)*base69 + (53941415023019774431/1106250000000000000000000000000000 : ℝ)*base72 + (90245100071033/22125000000000000000000000000 : ℝ)*base73 + (87782093716267725569/1106250000000000000000000000000000 : ℝ)*base75 + (12627282673548975569/1106250000000000000000000000000000 : ℝ)*base77 + (17649747567423975569/1106250000000000000000000000000000 : ℝ)*base79 + (99918682841033/22125000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (19487567/2500000000000000000000 : ℝ)*base90 + (19487567/2500000000000000000000 : ℝ)*base92 + (19487567/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1554_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1383/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1554_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1554_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (991/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1554_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1554_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1554_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4603/1024 : ℝ) ≤ p) (hpb : p ≤ (4605/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41685679/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (991/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5363/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2767/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1554_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
