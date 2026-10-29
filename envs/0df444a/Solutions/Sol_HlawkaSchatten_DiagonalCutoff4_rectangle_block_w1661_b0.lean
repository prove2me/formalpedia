-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1661_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:23.55338+00:00
-- url     : https://prove2.me/submissions/39e79c35-e843-4124-b6c9-7829501b27cc

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
theorem support_rectangle_w1661_s0_0 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1473548277/10000000000 : ℝ)*x 0 + (5771834567/10000000000 : ℝ)*x 1 + (2464465563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1473548277/10000000000 : ℝ)^4963 ≤ (2239281393819/25000000000000 : ℝ)^3939 := by
    have hnat : (1473548277 : ℕ)^4963*25000000000000^3939 ≤ 2239281393819^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473548277 10000000000 2239281393819 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5771834567/10000000000 : ℝ)^4963 ≤ (10006771000327/20000000000000 : ℝ)^3939 := by
    have hnat : (5771834567 : ℕ)^4963*20000000000000^3939 ≤ 10006771000327^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5771834567 10000000000 10006771000327 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2464465563/5000000000 : ℝ)^4963 ≤ (4100901940611/10000000000000 : ℝ)^3939 := by
    have hnat : (2464465563 : ℕ)^4963*10000000000000^3939 ≤ 4100901940611^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2464465563 5000000000 4100901940611 10000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1473548277/10000000000 : ℝ), (5771834567/10000000000 : ℝ), (2464465563/5000000000 : ℝ)] ![(2239281393819/25000000000000 : ℝ), (10006771000327/20000000000000 : ℝ), (4100901940611/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1473548277/10000000000 : ℝ)|^4963 ≤ (2239281393819/25000000000000 : ℝ)^3939
        have hw : |(-1473548277/10000000000 : ℝ)|=(1473548277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5771834567/10000000000 : ℝ)|^4963 ≤ (10006771000327/20000000000000 : ℝ)^3939
        have hw : |(5771834567/10000000000 : ℝ)|=(5771834567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2464465563/5000000000 : ℝ)|^4963 ≤ (4100901940611/10000000000000 : ℝ)^3939
        have hw : |(2464465563/5000000000 : ℝ)|=(2464465563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s0_1 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2716599969/5000000000 : ℝ)*x 0 + (-967607361/5000000000 : ℝ)*x 1 + (985786363/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2716599969/5000000000 : ℝ)^4963 ≤ (4636385963587/10000000000000 : ℝ)^3939 := by
    have hnat : (2716599969 : ℕ)^4963*10000000000000^3939 ≤ 4636385963587^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716599969 5000000000 4636385963587 10000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (967607361/5000000000 : ℝ)^4963 ≤ (789194607433/6250000000000 : ℝ)^3939 := by
    have hnat : (967607361 : ℕ)^4963*6250000000000^3939 ≤ 789194607433^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967607361 5000000000 789194607433 6250000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (985786363/2000000000 : ℝ)^4963 ≤ (41009026628887/100000000000000 : ℝ)^3939 := by
    have hnat : (985786363 : ℕ)^4963*100000000000000^3939 ≤ 41009026628887^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985786363 2000000000 41009026628887 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2716599969/5000000000 : ℝ), (-967607361/5000000000 : ℝ), (985786363/2000000000 : ℝ)] ![(4636385963587/10000000000000 : ℝ), (789194607433/6250000000000 : ℝ), (41009026628887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2716599969/5000000000 : ℝ)|^4963 ≤ (4636385963587/10000000000000 : ℝ)^3939
        have hw : |(2716599969/5000000000 : ℝ)|=(2716599969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-967607361/5000000000 : ℝ)|^4963 ≤ (789194607433/6250000000000 : ℝ)^3939
        have hw : |(-967607361/5000000000 : ℝ)|=(967607361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(985786363/2000000000 : ℝ)|^4963 ≤ (41009026628887/100000000000000 : ℝ)^3939
        have hw : |(985786363/2000000000 : ℝ)|=(985786363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s0_2 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1358300349/2500000000 : ℝ)*x 0 + (197157233/400000000 : ℝ)*x 1 + (-967607039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1358300349/2500000000 : ℝ)^4963 ≤ (1448871103501/3125000000000 : ℝ)^3939 := by
    have hnat : (1358300349 : ℕ)^4963*3125000000000^3939 ≤ 1448871103501^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358300349 2500000000 1448871103501 3125000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197157233/400000000 : ℝ)^4963 ≤ (10252254062683/25000000000000 : ℝ)^3939 := by
    have hnat : (197157233 : ℕ)^4963*25000000000000^3939 ≤ 10252254062683^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197157233 400000000 10252254062683 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967607039/5000000000 : ℝ)^4963 ≤ (12627108424499/100000000000000 : ℝ)^3939 := by
    have hnat : (967607039 : ℕ)^4963*100000000000000^3939 ≤ 12627108424499^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967607039 5000000000 12627108424499 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1358300349/2500000000 : ℝ), (197157233/400000000 : ℝ), (-967607039/5000000000 : ℝ)] ![(1448871103501/3125000000000 : ℝ), (10252254062683/25000000000000 : ℝ), (12627108424499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1358300349/2500000000 : ℝ)|^4963 ≤ (1448871103501/3125000000000 : ℝ)^3939
        have hw : |(1358300349/2500000000 : ℝ)|=(1358300349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(197157233/400000000 : ℝ)|^4963 ≤ (10252254062683/25000000000000 : ℝ)^3939
        have hw : |(197157233/400000000 : ℝ)|=(197157233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-967607039/5000000000 : ℝ)|^4963 ≤ (12627108424499/100000000000000 : ℝ)^3939
        have hw : |(-967607039/5000000000 : ℝ)|=(967607039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s0_3 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2042748307/5000000000 : ℝ)*x 0 + (771364761/2500000000 : ℝ)*x 1 + (26482561/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2042748307/5000000000 : ℝ)^4963 ≤ (16186477155077/50000000000000 : ℝ)^3939 := by
    have hnat : (2042748307 : ℕ)^4963*50000000000000^3939 ≤ 16186477155077^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042748307 5000000000 16186477155077 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (771364761/2500000000 : ℝ)^4963 ≤ (22727992687573/100000000000000 : ℝ)^3939 := by
    have hnat : (771364761 : ℕ)^4963*100000000000000^3939 ≤ 22727992687573^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771364761 2500000000 22727992687573 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26482561/50000000 : ℝ)^4963 ≤ (22449526493571/50000000000000 : ℝ)^3939 := by
    have hnat : (26482561 : ℕ)^4963*50000000000000^3939 ≤ 22449526493571^3939*50000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26482561 50000000 22449526493571 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2042748307/5000000000 : ℝ), (771364761/2500000000 : ℝ), (26482561/50000000 : ℝ)] ![(16186477155077/50000000000000 : ℝ), (22727992687573/100000000000000 : ℝ), (22449526493571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2042748307/5000000000 : ℝ)|^4963 ≤ (16186477155077/50000000000000 : ℝ)^3939
        have hw : |(2042748307/5000000000 : ℝ)|=(2042748307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(771364761/2500000000 : ℝ)|^4963 ≤ (22727992687573/100000000000000 : ℝ)^3939
        have hw : |(771364761/2500000000 : ℝ)|=(771364761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(26482561/50000000 : ℝ)|^4963 ≤ (22449526493571/50000000000000 : ℝ)^3939
        have hw : |(26482561/50000000 : ℝ)|=(26482561/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s0_4 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-295144597/2000000000 : ℝ)*x 0 + (4949714787/10000000000 : ℝ)*x 1 + (230013601/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (295144597/2000000000 : ℝ)^4963 ≤ (2243446123541/25000000000000 : ℝ)^3939 := by
    have hnat : (295144597 : ℕ)^4963*25000000000000^3939 ≤ 2243446123541^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295144597 2000000000 2243446123541 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4949714787/10000000000 : ℝ)^4963 ≤ (10306753371627/25000000000000 : ℝ)^3939 := by
    have hnat : (4949714787 : ℕ)^4963*25000000000000^3939 ≤ 10306753371627^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4949714787 10000000000 10306753371627 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230013601/400000000 : ℝ)^4963 ≤ (49799202000881/100000000000000 : ℝ)^3939 := by
    have hnat : (230013601 : ℕ)^4963*100000000000000^3939 ≤ 49799202000881^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230013601 400000000 49799202000881 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-295144597/2000000000 : ℝ), (4949714787/10000000000 : ℝ), (230013601/400000000 : ℝ)] ![(2243446123541/25000000000000 : ℝ), (10306753371627/25000000000000 : ℝ), (49799202000881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-295144597/2000000000 : ℝ)|^4963 ≤ (2243446123541/25000000000000 : ℝ)^3939
        have hw : |(-295144597/2000000000 : ℝ)|=(295144597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4949714787/10000000000 : ℝ)|^4963 ≤ (10306753371627/25000000000000 : ℝ)^3939
        have hw : |(4949714787/10000000000 : ℝ)|=(4949714787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230013601/400000000 : ℝ)|^4963 ≤ (49799202000881/100000000000000 : ℝ)^3939
        have hw : |(230013601/400000000 : ℝ)|=(230013601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s0_5 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203280221/10000000000 : ℝ)*x 0 + (-556903677/5000000000 : ℝ)*x 1 + (1437584537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203280221/10000000000 : ℝ)^4963 ≤ (21952772649321/50000000000000 : ℝ)^3939 := by
    have hnat : (5203280221 : ℕ)^4963*50000000000000^3939 ≤ 21952772649321^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203280221 10000000000 21952772649321 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (556903677/5000000000 : ℝ)^4963 ≤ (157381829339/2500000000000 : ℝ)^3939 := by
    have hnat : (556903677 : ℕ)^4963*2500000000000^3939 ≤ 157381829339^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556903677 5000000000 157381829339 2500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1437584537/2500000000 : ℝ)^4963 ≤ (49799181519869/100000000000000 : ℝ)^3939 := by
    have hnat : (1437584537 : ℕ)^4963*100000000000000^3939 ≤ 49799181519869^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1437584537 2500000000 49799181519869 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203280221/10000000000 : ℝ), (-556903677/5000000000 : ℝ), (1437584537/2500000000 : ℝ)] ![(21952772649321/50000000000000 : ℝ), (157381829339/2500000000000 : ℝ), (49799181519869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203280221/10000000000 : ℝ)|^4963 ≤ (21952772649321/50000000000000 : ℝ)^3939
        have hw : |(5203280221/10000000000 : ℝ)|=(5203280221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-556903677/5000000000 : ℝ)|^4963 ≤ (157381829339/2500000000000 : ℝ)^3939
        have hw : |(-556903677/5000000000 : ℝ)|=(556903677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1437584537/2500000000 : ℝ)|^4963 ≤ (49799181519869/100000000000000 : ℝ)^3939
        have hw : |(1437584537/2500000000 : ℝ)|=(1437584537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s0_6 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203279503/10000000000 : ℝ)*x 0 + (718792243/1250000000 : ℝ)*x 1 + (-556904369/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203279503/10000000000 : ℝ)^4963 ≤ (21952768832561/50000000000000 : ℝ)^3939 := by
    have hnat : (5203279503 : ℕ)^4963*50000000000000^3939 ≤ 21952768832561^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203279503 10000000000 21952768832561 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718792243/1250000000 : ℝ)^4963 ≤ (49799179293909/100000000000000 : ℝ)^3939 := by
    have hnat : (718792243 : ℕ)^4963*100000000000000^3939 ≤ 49799179293909^3939*1250000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718792243 1250000000 49799179293909 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (556904369/5000000000 : ℝ)^4963 ≤ (6295283029521/100000000000000 : ℝ)^3939 := by
    have hnat : (556904369 : ℕ)^4963*100000000000000^3939 ≤ 6295283029521^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      556904369 5000000000 6295283029521 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203279503/10000000000 : ℝ), (718792243/1250000000 : ℝ), (-556904369/5000000000 : ℝ)] ![(21952768832561/50000000000000 : ℝ), (49799179293909/100000000000000 : ℝ), (6295283029521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203279503/10000000000 : ℝ)|^4963 ≤ (21952768832561/50000000000000 : ℝ)^3939
        have hw : |(5203279503/10000000000 : ℝ)|=(5203279503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(718792243/1250000000 : ℝ)|^4963 ≤ (49799179293909/100000000000000 : ℝ)^3939
        have hw : |(718792243/1250000000 : ℝ)|=(718792243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-556904369/5000000000 : ℝ)|^4963 ≤ (6295283029521/100000000000000 : ℝ)^3939
        have hw : |(-556904369/5000000000 : ℝ)|=(556904369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s0_7 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4091200289/10000000000 : ℝ)*x 0 + (2620997047/5000000000 : ℝ)*x 1 + (314184523/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4091200289/10000000000 : ℝ)^4963 ≤ (32429908977557/100000000000000 : ℝ)^3939 := by
    have hnat : (4091200289 : ℕ)^4963*100000000000000^3939 ≤ 32429908977557^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4091200289 10000000000 32429908977557 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620997047/5000000000 : ℝ)^4963 ≤ (22158767382863/50000000000000 : ℝ)^3939 := by
    have hnat : (2620997047 : ℕ)^4963*50000000000000^3939 ≤ 22158767382863^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620997047 5000000000 22158767382863 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314184523/1000000000 : ℝ)^4963 ≤ (2906569529141/12500000000000 : ℝ)^3939 := by
    have hnat : (314184523 : ℕ)^4963*12500000000000^3939 ≤ 2906569529141^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314184523 1000000000 2906569529141 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4091200289/10000000000 : ℝ), (2620997047/5000000000 : ℝ), (314184523/1000000000 : ℝ)] ![(32429908977557/100000000000000 : ℝ), (22158767382863/50000000000000 : ℝ), (2906569529141/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4091200289/10000000000 : ℝ)|^4963 ≤ (32429908977557/100000000000000 : ℝ)^3939
        have hw : |(4091200289/10000000000 : ℝ)|=(4091200289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620997047/5000000000 : ℝ)|^4963 ≤ (22158767382863/50000000000000 : ℝ)^3939
        have hw : |(2620997047/5000000000 : ℝ)|=(2620997047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314184523/1000000000 : ℝ)|^4963 ≤ (2906569529141/12500000000000 : ℝ)^3939
        have hw : |(314184523/1000000000 : ℝ)|=(314184523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1661_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2527/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11563/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4959/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4959 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4959*1^1024 ≤ 0^1024*1^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4959/1024 : ℝ) ≤ (591339242474825337/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4959 ≤ (591339242474825337/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4959*50000000000000000000^1024 ≤ 591339242474825337^1024*5^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 591339242474825337 50000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (591339242474825337/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4959 := by
      have hnat : (1 : ℕ)^1024*1^4959 ≤ 1^4959*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50591339242474825337/50000000000000000000 : ℝ) ≤ (2506076930473701/2500000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (50591339242474825337/50000000000000000000 : ℝ)^1024 ≤ (2506076930473701/2500000000000000 : ℝ)^4959 := by
      have hnat : (50591339242474825337 : ℕ)^1024*2500000000000000^4959 ≤ 2506076930473701^4959*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50591339242474825337 50000000000000000000 2506076930473701 2500000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2506076930473701/2500000000000000 : ℝ)) (X := (50591339242474825337/50000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25591339242474825337/25000000000000000000 : ℝ) ≤ (1256076930473701/1250000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (25591339242474825337/25000000000000000000 : ℝ)^1024 ≤ (1256076930473701/1250000000000000 : ℝ)^4959 := by
      have hnat : (25591339242474825337 : ℕ)^1024*1250000000000000^4959 ≤ 1256076930473701^4959*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25591339242474825337 25000000000000000000 1256076930473701 1250000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256076930473701/1250000000000000 : ℝ)) (X := (25591339242474825337/25000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6076930473701/1000000000000000 : ℝ)*(0 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6076930473701/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(591339242474825337/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6076930473701/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4959/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6076930473701/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2506076930473701/2500000000000000 : ℝ) by norm_num, show 1+(591339242474825337/50000000000000000000 : ℝ)+(0 : ℝ)=(50591339242474825337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(591339242474825337/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6076930473701/1000000000000000 : ℝ)*(2/5 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6076930473701/1000000000000000 : ℝ)*(2/5 : ℝ)=(1256076930473701/1250000000000000 : ℝ) by norm_num, show 1+2*(591339242474825337/50000000000000000000 : ℝ)=(25591339242474825337/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6076930473701/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6076930473701/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6076930473701/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6076930473701/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6076930473701/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6076930473701/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1473548277/10000000000 : ℝ)*X 0 0+(5771834567/10000000000 : ℝ)*X 0 1+(2464465563/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2716599969/5000000000 : ℝ)*X 1 0+(-967607361/5000000000 : ℝ)*X 1 1+(985786363/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1358300349/2500000000 : ℝ)*X 2 0+(197157233/400000000 : ℝ)*X 2 1+(-967607039/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2042748307/5000000000 : ℝ)*X 0 0+(771364761/2500000000 : ℝ)*X 0 1+(26482561/50000000 : ℝ)*X 0 2+(2042748307/5000000000 : ℝ)*X 1 0+(771364761/2500000000 : ℝ)*X 1 1+(26482561/50000000 : ℝ)*X 1 2+(2042748307/5000000000 : ℝ)*X 2 0+(771364761/2500000000 : ℝ)*X 2 1+(26482561/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-295144597/2000000000 : ℝ)*X 0 0+(4949714787/10000000000 : ℝ)*X 0 1+(230013601/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5203280221/10000000000 : ℝ)*X 1 0+(-556903677/5000000000 : ℝ)*X 1 1+(1437584537/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5203279503/10000000000 : ℝ)*X 2 0+(718792243/1250000000 : ℝ)*X 2 1+(-556904369/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4091200289/10000000000 : ℝ)*X 0 0+(2620997047/5000000000 : ℝ)*X 0 1+(314184523/1000000000 : ℝ)*X 0 2+(4091200289/10000000000 : ℝ)*X 1 0+(2620997047/5000000000 : ℝ)*X 1 1+(314184523/1000000000 : ℝ)*X 1 2+(4091200289/10000000000 : ℝ)*X 2 0+(2620997047/5000000000 : ℝ)*X 2 1+(314184523/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (27878233780132450078341/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21969967/20000000000000 : ℝ)*(base1) + (19745107/6250000000000 : ℝ)*(base19) + (278891963/50000000000000 : ℝ)*(base23) + (76502567/100000000000000 : ℝ)*(base24) + (24167959/50000000000000 : ℝ)*(upper5) + (409663436030651/50000000000000 : ℝ)*(major0) + (409663436030651/50000000000000 : ℝ)*(major1) + (409663436030651/50000000000000 : ℝ)*(major2) + (296594180727951/25000000000000 : ℝ)*(sp0) + (593189291748231/50000000000000 : ℝ)*(sp1) + (7414864157073/625000000000 : ℝ)*(sp2) + (3618190887273/800000000000 : ℝ)*(sp3) + (457271241/20000000000000 : ℝ)*(sp4) + (49975219/6250000000000 : ℝ)*(sp7) + (90454954072493/20000000000000 : ℝ)*(f.failure) + (593189449709087/50000000000000 : ℝ)*(f.sum) + (98883041084351/25000000000000000000000000000 : ℝ)*base65 + (185276881459351/50000000000000000000000000000 : ℝ)*base67 + (138566217959351/50000000000000000000000000000 : ℝ)*base69 + (275240847309351/50000000000000000000000000000 : ℝ)*base71 + (128148377609351/25000000000000000000000000000 : ℝ)*base73 + (119330112909351/50000000000000000000000000000 : ℝ)*base75 + (438330551109351/50000000000000000000000000000 : ℝ)*base77 + (546336691609351/50000000000000000000000000000 : ℝ)*base79 + (100099588409351/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3076587/1000000000000000000000 : ℝ)*base90 + (3076587/1000000000000000000000 : ℝ)*base92 + (3076587/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (627841311187815567278091/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1977253673/100000000000000 : ℝ)*(base19) + (864162459/50000000000000 : ℝ)*(base23) + (1384537/781250000000 : ℝ)*(base32) + (234050521/100000000000000 : ℝ)*(upper3) + (15546097/10000000000000 : ℝ)*(upper5) + (862589639953797/100000000000000 : ℝ)*(major0) + (862589639953797/100000000000000 : ℝ)*(major1) + (862589639953797/100000000000000 : ℝ)*(major2) + (4526065273/100000000000000 : ℝ)*(sp1) + (1396523471/50000000000000 : ℝ)*(sp2) + (1249022708496947/100000000000000 : ℝ)*(sp4) + (1249016205178001/100000000000000 : ℝ)*(sp5) + (1249018187125087/100000000000000 : ℝ)*(sp6) + (238077987814517/50000000000000 : ℝ)*(sp7) + (47615615284977/10000000000000 : ℝ)*(f.failure) + (1249022708496947/100000000000000 : ℝ)*(f.sum) + (65729237957303/50000000000000000000000000000 : ℝ)*base66 + (75320915092697/100000000000000000000000000000 : ℝ)*base67 + (137957814092697/100000000000000000000000000000 : ℝ)*base69 + (186637248507303/100000000000000000000000000000 : ℝ)*base72 + (233738873207303/50000000000000000000000000000 : ℝ)*base74 + (816693917292697/100000000000000000000000000000 : ℝ)*base75 + (111667601692697/100000000000000000000000000000 : ℝ)*base77 + (171727616192697/100000000000000000000000000000 : ℝ)*base79 + (149838443307303/50000000000000000000000000000 : ℝ)*base82 + (2380857/500000000000000000000 : ℝ)*base89 + (2380857/500000000000000000000 : ℝ)*base91 + (2380857/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1661_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2527/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11563/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1661_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1661_s1_0 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1574960887/10000000000 : ℝ)*x 0 + (2744130091/5000000000 : ℝ)*x 1 + (5146496821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1574960887/10000000000 : ℝ)^4963 ≤ (4870330672989/50000000000000 : ℝ)^3939 := by
    have hnat : (1574960887 : ℕ)^4963*50000000000000^3939 ≤ 4870330672989^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1574960887 10000000000 4870330672989 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744130091/5000000000 : ℝ)^4963 ≤ (46956635612851/100000000000000 : ℝ)^3939 := by
    have hnat : (2744130091 : ℕ)^4963*100000000000000^3939 ≤ 46956635612851^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744130091 5000000000 46956635612851 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5146496821/10000000000 : ℝ)^4963 ≤ (21651351514361/50000000000000 : ℝ)^3939 := by
    have hnat : (5146496821 : ℕ)^4963*50000000000000^3939 ≤ 21651351514361^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146496821 10000000000 21651351514361 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1574960887/10000000000 : ℝ), (2744130091/5000000000 : ℝ), (5146496821/10000000000 : ℝ)] ![(4870330672989/50000000000000 : ℝ), (46956635612851/100000000000000 : ℝ), (21651351514361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1574960887/10000000000 : ℝ)|^4963 ≤ (4870330672989/50000000000000 : ℝ)^3939
        have hw : |(-1574960887/10000000000 : ℝ)|=(1574960887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744130091/5000000000 : ℝ)|^4963 ≤ (46956635612851/100000000000000 : ℝ)^3939
        have hw : |(2744130091/5000000000 : ℝ)|=(2744130091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5146496821/10000000000 : ℝ)|^4963 ≤ (21651351514361/50000000000000 : ℝ)^3939
        have hw : |(5146496821/10000000000 : ℝ)|=(5146496821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s1_1 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107155377/200000000 : ℝ)*x 0 + (-87619533/500000000 : ℝ)*x 1 + (25732483/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107155377/200000000 : ℝ)^4963 ≤ (9110861275677/20000000000000 : ℝ)^3939 := by
    have hnat : (107155377 : ℕ)^4963*20000000000000^3939 ≤ 9110861275677^3939*200000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107155377 200000000 9110861275677 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87619533/500000000 : ℝ)^4963 ≤ (696437057227/6250000000000 : ℝ)^3939 := by
    have hnat : (87619533 : ℕ)^4963*6250000000000^3939 ≤ 696437057227^3939*500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87619533 500000000 696437057227 6250000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (25732483/50000000 : ℝ)^4963 ≤ (43302700685821/100000000000000 : ℝ)^3939 := by
    have hnat : (25732483 : ℕ)^4963*100000000000000^3939 ≤ 43302700685821^3939*50000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      25732483 50000000 43302700685821 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107155377/200000000 : ℝ), (-87619533/500000000 : ℝ), (25732483/50000000 : ℝ)] ![(9110861275677/20000000000000 : ℝ), (696437057227/6250000000000 : ℝ), (43302700685821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107155377/200000000 : ℝ)|^4963 ≤ (9110861275677/20000000000000 : ℝ)^3939
        have hw : |(107155377/200000000 : ℝ)|=(107155377/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87619533/500000000 : ℝ)|^4963 ≤ (696437057227/6250000000000 : ℝ)^3939
        have hw : |(-87619533/500000000 : ℝ)|=(87619533/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(25732483/50000000 : ℝ)|^4963 ≤ (43302700685821/100000000000000 : ℝ)^3939
        have hw : |(25732483/50000000 : ℝ)|=(25732483/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s1_2 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357768301/10000000000 : ℝ)*x 0 + (5146497183/10000000000 : ℝ)*x 1 + (-54762207/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357768301/10000000000 : ℝ)^4963 ≤ (5694287562131/12500000000000 : ℝ)^3939 := by
    have hnat : (5357768301 : ℕ)^4963*12500000000000^3939 ≤ 5694287562131^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357768301 10000000000 5694287562131 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5146497183/10000000000 : ℝ)^4963 ≤ (21651353433207/50000000000000 : ℝ)^3939 := by
    have hnat : (5146497183 : ℕ)^4963*50000000000000^3939 ≤ 21651353433207^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5146497183 10000000000 21651353433207 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54762207/312500000 : ℝ)^4963 ≤ (1392874078401/12500000000000 : ℝ)^3939 := by
    have hnat : (54762207 : ℕ)^4963*12500000000000^3939 ≤ 1392874078401^3939*312500000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54762207 312500000 1392874078401 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357768301/10000000000 : ℝ), (5146497183/10000000000 : ℝ), (-54762207/312500000 : ℝ)] ![(5694287562131/12500000000000 : ℝ), (21651353433207/50000000000000 : ℝ), (1392874078401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357768301/10000000000 : ℝ)|^4963 ≤ (5694287562131/12500000000000 : ℝ)^3939
        have hw : |(5357768301/10000000000 : ℝ)|=(5357768301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5146497183/10000000000 : ℝ)|^4963 ≤ (21651353433207/50000000000000 : ℝ)^3939
        have hw : |(5146497183/10000000000 : ℝ)|=(5146497183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54762207/312500000 : ℝ)|^4963 ≤ (1392874078401/12500000000000 : ℝ)^3939
        have hw : |(-54762207/312500000 : ℝ)|=(54762207/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s1_3 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4165777047/10000000000 : ℝ)*x 0 + (466838561/1250000000 : ℝ)*x 1 + (4631201177/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165777047/10000000000 : ℝ)^4963 ≤ (33176495247747/100000000000000 : ℝ)^3939 := by
    have hnat : (4165777047 : ℕ)^4963*100000000000000^3939 ≤ 33176495247747^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165777047 10000000000 33176495247747 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466838561/1250000000 : ℝ)^4963 ≤ (28910703239813/100000000000000 : ℝ)^3939 := by
    have hnat : (466838561 : ℕ)^4963*100000000000000^3939 ≤ 28910703239813^3939*1250000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466838561 1250000000 28910703239813 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4631201177/10000000000 : ℝ)^4963 ≤ (9478200375339/25000000000000 : ℝ)^3939 := by
    have hnat : (4631201177 : ℕ)^4963*25000000000000^3939 ≤ 9478200375339^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4631201177 10000000000 9478200375339 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165777047/10000000000 : ℝ), (466838561/1250000000 : ℝ), (4631201177/10000000000 : ℝ)] ![(33176495247747/100000000000000 : ℝ), (28910703239813/100000000000000 : ℝ), (9478200375339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165777047/10000000000 : ℝ)|^4963 ≤ (33176495247747/100000000000000 : ℝ)^3939
        have hw : |(4165777047/10000000000 : ℝ)|=(4165777047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(466838561/1250000000 : ℝ)|^4963 ≤ (28910703239813/100000000000000 : ℝ)^3939
        have hw : |(466838561/1250000000 : ℝ)|=(466838561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4631201177/10000000000 : ℝ)|^4963 ≤ (9478200375339/25000000000000 : ℝ)^3939
        have hw : |(4631201177/10000000000 : ℝ)|=(4631201177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s1_4 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63004129/400000000 : ℝ)*x 0 + (1287476719/2500000000 : ℝ)*x 1 + (2742401593/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63004129/400000000 : ℝ)^4963 ≤ (9741770528269/100000000000000 : ℝ)^3939 := by
    have hnat : (63004129 : ℕ)^4963*100000000000000^3939 ≤ 9741770528269^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63004129 400000000 9741770528269 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1287476719/2500000000 : ℝ)^4963 ≤ (43338857363247/100000000000000 : ℝ)^3939 := by
    have hnat : (1287476719 : ℕ)^4963*100000000000000^3939 ≤ 43338857363247^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287476719 2500000000 43338857363247 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2742401593/5000000000 : ℝ)^4963 ≤ (4691937209193/10000000000000 : ℝ)^3939 := by
    have hnat : (2742401593 : ℕ)^4963*10000000000000^3939 ≤ 4691937209193^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742401593 5000000000 4691937209193 10000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63004129/400000000 : ℝ), (1287476719/2500000000 : ℝ), (2742401593/5000000000 : ℝ)] ![(9741770528269/100000000000000 : ℝ), (43338857363247/100000000000000 : ℝ), (4691937209193/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63004129/400000000 : ℝ)|^4963 ≤ (9741770528269/100000000000000 : ℝ)^3939
        have hw : |(-63004129/400000000 : ℝ)|=(63004129/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1287476719/2500000000 : ℝ)|^4963 ≤ (43338857363247/100000000000000 : ℝ)^3939
        have hw : |(1287476719/2500000000 : ℝ)|=(1287476719/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2742401593/5000000000 : ℝ)|^4963 ≤ (4691937209193/10000000000000 : ℝ)^3939
        have hw : |(2742401593/5000000000 : ℝ)|=(2742401593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s1_5 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266291641/10000000000 : ℝ)*x 0 + (-1414084583/10000000000 : ℝ)*x 1 + (5484803193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266291641/10000000000 : ℝ)^4963 ≤ (8915302338507/20000000000000 : ℝ)^3939 := by
    have hnat : (5266291641 : ℕ)^4963*20000000000000^3939 ≤ 8915302338507^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266291641 10000000000 8915302338507 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1414084583/10000000000 : ℝ)^4963 ≤ (8504116125999/100000000000000 : ℝ)^3939 := by
    have hnat : (1414084583 : ℕ)^4963*100000000000000^3939 ≤ 8504116125999^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414084583 10000000000 8504116125999 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5484803193/10000000000 : ℝ)^4963 ≤ (23459686083689/50000000000000 : ℝ)^3939 := by
    have hnat : (5484803193 : ℕ)^4963*50000000000000^3939 ≤ 23459686083689^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484803193 10000000000 23459686083689 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266291641/10000000000 : ℝ), (-1414084583/10000000000 : ℝ), (5484803193/10000000000 : ℝ)] ![(8915302338507/20000000000000 : ℝ), (8504116125999/100000000000000 : ℝ), (23459686083689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266291641/10000000000 : ℝ)|^4963 ≤ (8915302338507/20000000000000 : ℝ)^3939
        have hw : |(5266291641/10000000000 : ℝ)|=(5266291641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1414084583/10000000000 : ℝ)|^4963 ≤ (8504116125999/100000000000000 : ℝ)^3939
        have hw : |(-1414084583/10000000000 : ℝ)|=(1414084583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5484803193/10000000000 : ℝ)|^4963 ≤ (23459686083689/50000000000000 : ℝ)^3939
        have hw : |(5484803193/10000000000 : ℝ)|=(5484803193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s1_6 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266291639/10000000000 : ℝ)*x 0 + (5484803197/10000000000 : ℝ)*x 1 + (-1414084579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266291639/10000000000 : ℝ)^4963 ≤ (22288255835603/50000000000000 : ℝ)^3939 := by
    have hnat : (5266291639 : ℕ)^4963*50000000000000^3939 ≤ 22288255835603^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266291639 10000000000 22288255835603 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5484803197/10000000000 : ℝ)^4963 ≤ (46919372210491/100000000000000 : ℝ)^3939 := by
    have hnat : (5484803197 : ℕ)^4963*100000000000000^3939 ≤ 46919372210491^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5484803197 10000000000 46919372210491 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414084579/10000000000 : ℝ)^4963 ≤ (850411609569/10000000000000 : ℝ)^3939 := by
    have hnat : (1414084579 : ℕ)^4963*10000000000000^3939 ≤ 850411609569^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414084579 10000000000 850411609569 10000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266291639/10000000000 : ℝ), (5484803197/10000000000 : ℝ), (-1414084579/10000000000 : ℝ)] ![(22288255835603/50000000000000 : ℝ), (46919372210491/100000000000000 : ℝ), (850411609569/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266291639/10000000000 : ℝ)|^4963 ≤ (22288255835603/50000000000000 : ℝ)^3939
        have hw : |(5266291639/10000000000 : ℝ)|=(5266291639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5484803197/10000000000 : ℝ)|^4963 ≤ (46919372210491/100000000000000 : ℝ)^3939
        have hw : |(5484803197/10000000000 : ℝ)|=(5484803197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1414084579/10000000000 : ℝ)|^4963 ≤ (850411609569/10000000000000 : ℝ)^3939
        have hw : |(-1414084579/10000000000 : ℝ)|=(1414084579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s1_7 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4166151417/10000000000 : ℝ)*x 0 + (462225647/1000000000 : ℝ)*x 1 + (3743777337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4166151417/10000000000 : ℝ)^4963 ≤ (33180251881787/100000000000000 : ℝ)^3939 := by
    have hnat : (4166151417 : ℕ)^4963*100000000000000^3939 ≤ 33180251881787^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166151417 10000000000 33180251881787 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462225647/1000000000 : ℝ)^4963 ≤ (1181892624871/3125000000000 : ℝ)^3939 := by
    have hnat : (462225647 : ℕ)^4963*3125000000000^3939 ≤ 1181892624871^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462225647 1000000000 1181892624871 3125000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3743777337/10000000000 : ℝ)^4963 ≤ (28999184110049/100000000000000 : ℝ)^3939 := by
    have hnat : (3743777337 : ℕ)^4963*100000000000000^3939 ≤ 28999184110049^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3743777337 10000000000 28999184110049 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4166151417/10000000000 : ℝ), (462225647/1000000000 : ℝ), (3743777337/10000000000 : ℝ)] ![(33180251881787/100000000000000 : ℝ), (1181892624871/3125000000000 : ℝ), (28999184110049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4166151417/10000000000 : ℝ)|^4963 ≤ (33180251881787/100000000000000 : ℝ)^3939
        have hw : |(4166151417/10000000000 : ℝ)|=(4166151417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(462225647/1000000000 : ℝ)|^4963 ≤ (1181892624871/3125000000000 : ℝ)^3939
        have hw : |(462225647/1000000000 : ℝ)|=(462225647/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3743777337/10000000000 : ℝ)|^4963 ≤ (28999184110049/100000000000000 : ℝ)^3939
        have hw : |(3743777337/10000000000 : ℝ)|=(3743777337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1661_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11563/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9901/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1073/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11563/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11563/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2527/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11563/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11563/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2527/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11563/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11563/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2527/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2527/50000 : ℝ) ^ (4959/1024 : ℝ) ≤ (52722884562881/100000000000000000000 : ℝ) := by
    have hpowers : (2527/50000 : ℝ)^4959 ≤ (52722884562881/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2527 : ℕ)^4959*100000000000000000000^1024 ≤ 52722884562881^1024*50000^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2527 50000 52722884562881 100000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2527/50000 : ℝ)) (X := (52722884562881/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11563/50000 : ℝ) ^ (4959/1024 : ℝ) ≤ (8326891305554781/10000000000000000000 : ℝ) := by
    have hpowers : (11563/50000 : ℝ)^4959 ≤ (8326891305554781/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11563 : ℕ)^4959*10000000000000000000^1024 ≤ 8326891305554781^1024*50000^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11563 50000 8326891305554781 10000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11563/50000 : ℝ)) (X := (8326891305554781/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000052722884562881/50000000000000000000 : ℝ) ≤ (10000002177382989/10000000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (50000052722884562881/50000000000000000000 : ℝ)^1024 ≤ (10000002177382989/10000000000000000 : ℝ)^4959 := by
      have hnat : (50000052722884562881 : ℕ)^1024*10000000000000000^4959 ≤ 10000002177382989^4959*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000052722884562881 50000000000000000000 10000002177382989 10000000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002177382989/10000000000000000 : ℝ)) (X := (50000052722884562881/50000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100083321635940110691/100000000000000000000 : ℝ) ≤ (10001719967001231/10000000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (100083321635940110691/100000000000000000000 : ℝ)^1024 ≤ (10001719967001231/10000000000000000 : ℝ)^4959 := by
      have hnat : (100083321635940110691 : ℕ)^1024*10000000000000000^4959 ≤ 10001719967001231^4959*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100083321635940110691 100000000000000000000 10001719967001231 10000000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001719967001231/10000000000000000 : ℝ)) (X := (100083321635940110691/100000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5008326891305554781/5000000000000000000 : ℝ) ≤ (10003437756619473/10000000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (5008326891305554781/5000000000000000000 : ℝ)^1024 ≤ (10003437756619473/10000000000000000 : ℝ)^4959 := by
      have hnat : (5008326891305554781 : ℕ)^1024*10000000000000000^4959 ≤ 10003437756619473^4959*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5008326891305554781 5000000000000000000 10003437756619473 10000000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003437756619473/10000000000000000 : ℝ)) (X := (5008326891305554781/5000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(52722884562881/100000000000000000000 : ℝ) ≤ ((313719923493410047/313750000000000000 : ℝ)+2*(95432756569/100400000000000 : ℝ)*(2527/50000 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (313719923493410047/313750000000000000 : ℝ)+2*(95432756569/100400000000000 : ℝ)*(2527/50000 : ℝ)=(10000002177382989/10000000000000000 : ℝ) by norm_num, show 1+2*(52722884562881/100000000000000000000 : ℝ)=(50000052722884562881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8326891305554781/10000000000000000000 : ℝ)+(52722884562881/100000000000000000000 : ℝ) ≤ ((313719923493410047/313750000000000000 : ℝ)+(95432756569/100400000000000 : ℝ)*((11563/50000 : ℝ)+(2527/50000 : ℝ)))^(4959/1024 : ℝ) := by
    rw [show (313719923493410047/313750000000000000 : ℝ)+(95432756569/100400000000000 : ℝ)*((11563/50000 : ℝ)+(2527/50000 : ℝ))=(10001719967001231/10000000000000000 : ℝ) by norm_num, show 1+(8326891305554781/10000000000000000000 : ℝ)+(52722884562881/100000000000000000000 : ℝ)=(100083321635940110691/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8326891305554781/10000000000000000000 : ℝ) ≤ ((313719923493410047/313750000000000000 : ℝ)+2*(95432756569/100400000000000 : ℝ)*(11563/50000 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (313719923493410047/313750000000000000 : ℝ)+2*(95432756569/100400000000000 : ℝ)*(11563/50000 : ℝ)=(10003437756619473/10000000000000000 : ℝ) by norm_num, show 1+2*(8326891305554781/10000000000000000000 : ℝ)=(5008326891305554781/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (313719923493410047/313750000000000000 : ℝ)*(X 1 0+X 2 0)+(95432756569/100400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (2527/50000 : ℝ)) (hi := (11563/50000 : ℝ)) (c := (313719923493410047/313750000000000000 : ℝ)) (alpha := (95432756569/100400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (313719923493410047/313750000000000000 : ℝ)*(X 0 1+X 2 1)+(95432756569/100400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (2527/50000 : ℝ)) (hi := (11563/50000 : ℝ)) (c := (313719923493410047/313750000000000000 : ℝ)) (alpha := (95432756569/100400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (313719923493410047/313750000000000000 : ℝ)*(X 0 2+X 1 2)+(95432756569/100400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (2527/50000 : ℝ)) (hi := (11563/50000 : ℝ)) (c := (313719923493410047/313750000000000000 : ℝ)) (alpha := (95432756569/100400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1574960887/10000000000 : ℝ)*X 0 0+(2744130091/5000000000 : ℝ)*X 0 1+(5146496821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((107155377/200000000 : ℝ)*X 1 0+(-87619533/500000000 : ℝ)*X 1 1+(25732483/50000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5357768301/10000000000 : ℝ)*X 2 0+(5146497183/10000000000 : ℝ)*X 2 1+(-54762207/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4165777047/10000000000 : ℝ)*X 0 0+(466838561/1250000000 : ℝ)*X 0 1+(4631201177/10000000000 : ℝ)*X 0 2+(4165777047/10000000000 : ℝ)*X 1 0+(466838561/1250000000 : ℝ)*X 1 1+(4631201177/10000000000 : ℝ)*X 1 2+(4165777047/10000000000 : ℝ)*X 2 0+(466838561/1250000000 : ℝ)*X 2 1+(4631201177/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-63004129/400000000 : ℝ)*X 0 0+(1287476719/2500000000 : ℝ)*X 0 1+(2742401593/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266291641/10000000000 : ℝ)*X 1 0+(-1414084583/10000000000 : ℝ)*X 1 1+(5484803193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266291639/10000000000 : ℝ)*X 2 0+(5484803197/10000000000 : ℝ)*X 2 1+(-1414084579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4166151417/10000000000 : ℝ)*X 0 0+(462225647/1000000000 : ℝ)*X 0 1+(3743777337/10000000000 : ℝ)*X 0 2+(4166151417/10000000000 : ℝ)*X 1 0+(462225647/1000000000 : ℝ)*X 1 1+(3743777337/10000000000 : ℝ)*X 1 2+(4166151417/10000000000 : ℝ)*X 2 0+(462225647/1000000000 : ℝ)*X 2 1+(3743777337/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12225258234277046468757573/1568750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (416790977/20000000000000 : ℝ)*(base19) + (413971101/25000000000000 : ℝ)*(base23) + (79666719/25000000000000 : ℝ)*(upper3) + (68710757/100000000000000 : ℝ)*(upper4) + (103549301/50000000000000 : ℝ)*(upper5) + (202075691492139/10000000000000 : ℝ)*(major0) + (202075691492139/10000000000000 : ℝ)*(major1) + (202075691492139/10000000000000 : ℝ)*(major2) + (1463010778629653/50000000000000 : ℝ)*(sp0) + (292603803978481/10000000000000 : ℝ)*(sp1) + (731509616963823/25000000000000 : ℝ)*(sp2) + (69716588265257/6250000000000 : ℝ)*(sp3) + (18566480389/100000000000000 : ℝ)*(sp4) + (4017046261/50000000000000 : ℝ)*(sp7) + (223094689267327/20000000000000 : ℝ)*(f.failure) + (585208024747939/20000000000000 : ℝ)*(f.sum) + (592793151609/502000000000000000000000000 : ℝ)*base65 + (2465174279217523/784375000000000000000000000000 : ℝ)*base68 + (881337447763727/784375000000000000000000000000 : ℝ)*base69 + (364712927611273/784375000000000000000000000000 : ℝ)*base72 + (41575917701/502000000000000000000000000 : ℝ)*base74 + (60901194173773/784375000000000000000000000000 : ℝ)*base76 + (4452507078836273/784375000000000000000000000000 : ℝ)*base78 + (14803890307280023/784375000000000000000000000000 : ℝ)*base80 + (2625426523031/502000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (11897207/1000000000000000000000 : ℝ)*base89 + (11897207/1000000000000000000000 : ℝ)*base91 + (11897207/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53126885493419956295322519/7843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1064880997/100000000000000 : ℝ)*(base19) + (71783971/6250000000000 : ℝ)*(base23) + (31532597/20000000000000 : ℝ)*(upper3) + (232759/625000000000 : ℝ)*(lower4) + (37875737/25000000000000 : ℝ)*(upper5) + (1031082357388759/50000000000000 : ℝ)*(major0) + (1031082357388759/50000000000000 : ℝ)*(major1) + (1031082357388759/50000000000000 : ℝ)*(major2) + (9613822163/100000000000000 : ℝ)*(sp1) + (521222859/5000000000000 : ℝ)*(sp2) + (373249791457821/12500000000000 : ℝ)*(sp4) + (186624228309963/6250000000000 : ℝ)*(sp5) + (746496689665463/25000000000000 : ℝ)*(sp6) + (569165436060419/50000000000000 : ℝ)*(sp7) + (569165436060419/50000000000000 : ℝ)*(f.failure) + (373249791457821/12500000000000 : ℝ)*(f.sum) + (7249676436411/2510000000000000000000000000 : ℝ)*base65 + (21077955469172863/3921875000000000000000000000000 : ℝ)*base68 + (12814763393016613/3921875000000000000000000000000 : ℝ)*base70 + (1506871201202137/3921875000000000000000000000000 : ℝ)*base71 + (248124706289/2510000000000000000000000000 : ℝ)*base74 + (10172938671108387/3921875000000000000000000000000 : ℝ)*base75 + (8407532830516613/3921875000000000000000000000000 : ℝ)*base78 + (9354087519422863/3921875000000000000000000000000 : ℝ)*base80 + (2833978685091/2510000000000000000000000000 : ℝ)*base81 + (15173221/2500000000000000000000 : ℝ)*base90 + (15173221/2500000000000000000000 : ℝ)*base92 + (15173221/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1661_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11563/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2527/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9901/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1073/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1661_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1661_s2_0 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-791636487/5000000000 : ℝ)*x 0 + (5447247309/10000000000 : ℝ)*x 1 + (2591007303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (791636487/5000000000 : ℝ)^4963 ≤ (2451369420729/25000000000000 : ℝ)^3939 := by
    have hnat : (791636487 : ℕ)^4963*25000000000000^3939 ≤ 2451369420729^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791636487 5000000000 2451369420729 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447247309/10000000000 : ℝ)^4963 ≤ (46514945236691/100000000000000 : ℝ)^3939 := by
    have hnat : (5447247309 : ℕ)^4963*100000000000000^3939 ≤ 46514945236691^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447247309 10000000000 46514945236691 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591007303/5000000000 : ℝ)^4963 ≤ (1364986783203/3125000000000 : ℝ)^3939 := by
    have hnat : (2591007303 : ℕ)^4963*3125000000000^3939 ≤ 1364986783203^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591007303 5000000000 1364986783203 3125000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-791636487/5000000000 : ℝ), (5447247309/10000000000 : ℝ), (2591007303/5000000000 : ℝ)] ![(2451369420729/25000000000000 : ℝ), (46514945236691/100000000000000 : ℝ), (1364986783203/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-791636487/5000000000 : ℝ)|^4963 ≤ (2451369420729/25000000000000 : ℝ)^3939
        have hw : |(-791636487/5000000000 : ℝ)|=(791636487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447247309/10000000000 : ℝ)|^4963 ≤ (46514945236691/100000000000000 : ℝ)^3939
        have hw : |(5447247309/10000000000 : ℝ)|=(5447247309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591007303/5000000000 : ℝ)|^4963 ≤ (1364986783203/3125000000000 : ℝ)^3939
        have hw : |(2591007303/5000000000 : ℝ)|=(2591007303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s2_1 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346874777/10000000000 : ℝ)*x 0 + (-1719834833/10000000000 : ℝ)*x 1 + (207280571/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346874777/10000000000 : ℝ)^4963 ≤ (11359407752157/25000000000000 : ℝ)^3939 := by
    have hnat : (5346874777 : ℕ)^4963*25000000000000^3939 ≤ 11359407752157^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346874777 10000000000 11359407752157 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1719834833/10000000000 : ℝ)^4963 ≤ (10882795433431/100000000000000 : ℝ)^3939 := by
    have hnat : (1719834833 : ℕ)^4963*100000000000000^3939 ≤ 10882795433431^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719834833 10000000000 10882795433431 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (207280571/400000000 : ℝ)^4963 ≤ (21839786773583/50000000000000 : ℝ)^3939 := by
    have hnat : (207280571 : ℕ)^4963*50000000000000^3939 ≤ 21839786773583^3939*400000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207280571 400000000 21839786773583 50000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346874777/10000000000 : ℝ), (-1719834833/10000000000 : ℝ), (207280571/400000000 : ℝ)] ![(11359407752157/25000000000000 : ℝ), (10882795433431/100000000000000 : ℝ), (21839786773583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346874777/10000000000 : ℝ)|^4963 ≤ (11359407752157/25000000000000 : ℝ)^3939
        have hw : |(5346874777/10000000000 : ℝ)|=(5346874777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1719834833/10000000000 : ℝ)|^4963 ≤ (10882795433431/100000000000000 : ℝ)^3939
        have hw : |(-1719834833/10000000000 : ℝ)|=(1719834833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(207280571/400000000 : ℝ)|^4963 ≤ (21839786773583/50000000000000 : ℝ)^3939
        have hw : |(207280571/400000000 : ℝ)|=(207280571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s2_2 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346873173/10000000000 : ℝ)*x 0 + (2591007679/5000000000 : ℝ)*x 1 + (-214979443/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346873173/10000000000 : ℝ)^4963 ≤ (45437613834357/100000000000000 : ℝ)^3939 := by
    have hnat : (5346873173 : ℕ)^4963*100000000000000^3939 ≤ 45437613834357^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346873173 10000000000 45437613834357 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591007679/5000000000 : ℝ)^4963 ≤ (8735917009797/20000000000000 : ℝ)^3939 := by
    have hnat : (2591007679 : ℕ)^4963*20000000000000^3939 ≤ 8735917009797^3939*5000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591007679 5000000000 8735917009797 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214979443/1250000000 : ℝ)^4963 ≤ (2720700275527/25000000000000 : ℝ)^3939 := by
    have hnat : (214979443 : ℕ)^4963*25000000000000^3939 ≤ 2720700275527^3939*1250000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214979443 1250000000 2720700275527 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346873173/10000000000 : ℝ), (2591007679/5000000000 : ℝ), (-214979443/1250000000 : ℝ)] ![(45437613834357/100000000000000 : ℝ), (8735917009797/20000000000000 : ℝ), (2720700275527/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346873173/10000000000 : ℝ)|^4963 ≤ (45437613834357/100000000000000 : ℝ)^3939
        have hw : |(5346873173/10000000000 : ℝ)|=(5346873173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591007679/5000000000 : ℝ)|^4963 ≤ (8735917009797/20000000000000 : ℝ)^3939
        have hw : |(2591007679/5000000000 : ℝ)|=(2591007679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214979443/1250000000 : ℝ)|^4963 ≤ (2720700275527/25000000000000 : ℝ)^3939
        have hw : |(-214979443/1250000000 : ℝ)|=(214979443/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s2_3 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1042996983/2500000000 : ℝ)*x 0 + (383447089/1000000000 : ℝ)*x 1 + (3624167/8000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1042996983/2500000000 : ℝ)^4963 ≤ (33238830021833/100000000000000 : ℝ)^3939 := by
    have hnat : (1042996983 : ℕ)^4963*100000000000000^3939 ≤ 33238830021833^3939*2500000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042996983 2500000000 33238830021833 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383447089/1000000000 : ℝ)^4963 ≤ (7471772936863/25000000000000 : ℝ)^3939 := by
    have hnat : (383447089 : ℕ)^4963*25000000000000^3939 ≤ 7471772936863^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383447089 1000000000 7471772936863 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3624167/8000000 : ℝ)^4963 ≤ (36874078220237/100000000000000 : ℝ)^3939 := by
    have hnat : (3624167 : ℕ)^4963*100000000000000^3939 ≤ 36874078220237^3939*8000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3624167 8000000 36874078220237 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1042996983/2500000000 : ℝ), (383447089/1000000000 : ℝ), (3624167/8000000 : ℝ)] ![(33238830021833/100000000000000 : ℝ), (7471772936863/25000000000000 : ℝ), (36874078220237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1042996983/2500000000 : ℝ)|^4963 ≤ (33238830021833/100000000000000 : ℝ)^3939
        have hw : |(1042996983/2500000000 : ℝ)|=(1042996983/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(383447089/1000000000 : ℝ)|^4963 ≤ (7471772936863/25000000000000 : ℝ)^3939
        have hw : |(383447089/1000000000 : ℝ)|=(383447089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3624167/8000000 : ℝ)|^4963 ≤ (36874078220237/100000000000000 : ℝ)^3939
        have hw : |(3624167/8000000 : ℝ)|=(3624167/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s2_4 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1583339209/10000000000 : ℝ)*x 0 + (518407403/1000000000 : ℝ)*x 1 + (5445166189/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1583339209/10000000000 : ℝ)^4963 ≤ (9805994528909/100000000000000 : ℝ)^3939 := by
    have hnat : (1583339209 : ℕ)^4963*100000000000000^3939 ≤ 9805994528909^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583339209 10000000000 9805994528909 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518407403/1000000000 : ℝ)^4963 ≤ (10925362489617/25000000000000 : ℝ)^3939 := by
    have hnat : (518407403 : ℕ)^4963*25000000000000^3939 ≤ 10925362489617^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518407403 1000000000 10925362489617 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445166189/10000000000 : ℝ)^4963 ≤ (5811569435679/12500000000000 : ℝ)^3939 := by
    have hnat : (5445166189 : ℕ)^4963*12500000000000^3939 ≤ 5811569435679^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445166189 10000000000 5811569435679 12500000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1583339209/10000000000 : ℝ), (518407403/1000000000 : ℝ), (5445166189/10000000000 : ℝ)] ![(9805994528909/100000000000000 : ℝ), (10925362489617/25000000000000 : ℝ), (5811569435679/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1583339209/10000000000 : ℝ)|^4963 ≤ (9805994528909/100000000000000 : ℝ)^3939
        have hw : |(-1583339209/10000000000 : ℝ)|=(1583339209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(518407403/1000000000 : ℝ)|^4963 ≤ (10925362489617/25000000000000 : ℝ)^3939
        have hw : |(518407403/1000000000 : ℝ)|=(518407403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445166189/10000000000 : ℝ)|^4963 ≤ (5811569435679/12500000000000 : ℝ)^3939
        have hw : |(5445166189/10000000000 : ℝ)|=(5445166189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s2_5 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275926523/10000000000 : ℝ)*x 0 + (-1456684673/10000000000 : ℝ)*x 1 + (5445165257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275926523/10000000000 : ℝ)^4963 ≤ (357434334439/800000000000 : ℝ)^3939 := by
    have hnat : (5275926523 : ℕ)^4963*800000000000^3939 ≤ 357434334439^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275926523 10000000000 357434334439 800000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1456684673/10000000000 : ℝ)^4963 ≤ (8828162721599/100000000000000 : ℝ)^3939 := by
    have hnat : (1456684673 : ℕ)^4963*100000000000000^3939 ≤ 8828162721599^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1456684673 10000000000 8828162721599 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445165257/10000000000 : ℝ)^4963 ≤ (46492545458999/100000000000000 : ℝ)^3939 := by
    have hnat : (5445165257 : ℕ)^4963*100000000000000^3939 ≤ 46492545458999^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445165257 10000000000 46492545458999 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275926523/10000000000 : ℝ), (-1456684673/10000000000 : ℝ), (5445165257/10000000000 : ℝ)] ![(357434334439/800000000000 : ℝ), (8828162721599/100000000000000 : ℝ), (46492545458999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275926523/10000000000 : ℝ)|^4963 ≤ (357434334439/800000000000 : ℝ)^3939
        have hw : |(5275926523/10000000000 : ℝ)|=(5275926523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1456684673/10000000000 : ℝ)|^4963 ≤ (8828162721599/100000000000000 : ℝ)^3939
        have hw : |(-1456684673/10000000000 : ℝ)|=(1456684673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445165257/10000000000 : ℝ)|^4963 ≤ (46492545458999/100000000000000 : ℝ)^3939
        have hw : |(5445165257/10000000000 : ℝ)|=(5445165257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s2_6 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055185461/2000000000 : ℝ)*x 0 + (5445164849/10000000000 : ℝ)*x 1 + (-291336831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055185461/2000000000 : ℝ)^4963 ≤ (44679300148843/100000000000000 : ℝ)^3939 := by
    have hnat : (1055185461 : ℕ)^4963*100000000000000^3939 ≤ 44679300148843^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055185461 2000000000 44679300148843 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445164849/10000000000 : ℝ)^4963 ≤ (9298508213949/20000000000000 : ℝ)^3939 := by
    have hnat : (5445164849 : ℕ)^4963*20000000000000^3939 ≤ 9298508213949^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445164849 10000000000 9298508213949 20000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (291336831/2000000000 : ℝ)^4963 ≤ (8828158766177/100000000000000 : ℝ)^3939 := by
    have hnat : (291336831 : ℕ)^4963*100000000000000^3939 ≤ 8828158766177^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291336831 2000000000 8828158766177 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055185461/2000000000 : ℝ), (5445164849/10000000000 : ℝ), (-291336831/2000000000 : ℝ)] ![(44679300148843/100000000000000 : ℝ), (9298508213949/20000000000000 : ℝ), (8828158766177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055185461/2000000000 : ℝ)|^4963 ≤ (44679300148843/100000000000000 : ℝ)^3939
        have hw : |(1055185461/2000000000 : ℝ)|=(1055185461/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445164849/10000000000 : ℝ)|^4963 ≤ (9298508213949/20000000000000 : ℝ)^3939
        have hw : |(5445164849/10000000000 : ℝ)|=(5445164849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-291336831/2000000000 : ℝ)|^4963 ≤ (8828158766177/100000000000000 : ℝ)^3939
        have hw : |(-291336831/2000000000 : ℝ)|=(291336831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1661_s2_7 (p : ℝ) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4172164583/10000000000 : ℝ)*x 0 + (452480819/1000000000 : ℝ)*x 1 + (767985647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172164583/10000000000 : ℝ)^4963 ≤ (8310150827657/25000000000000 : ℝ)^3939 := by
    have hnat : (4172164583 : ℕ)^4963*25000000000000^3939 ≤ 8310150827657^3939*10000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172164583 10000000000 8310150827657 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452480819/1000000000 : ℝ)^4963 ≤ (9204675199787/25000000000000 : ℝ)^3939 := by
    have hnat : (452480819 : ℕ)^4963*25000000000000^3939 ≤ 9204675199787^3939*1000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452480819 1000000000 9204675199787 25000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (767985647/2000000000 : ℝ)^4963 ≤ (29940695873831/100000000000000 : ℝ)^3939 := by
    have hnat : (767985647 : ℕ)^4963*100000000000000^3939 ≤ 29940695873831^3939*2000000000^4963 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      767985647 2000000000 29940695873831 100000000000000 4963 3939 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4963/1024 : ℝ)) 4963 3939 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172164583/10000000000 : ℝ), (452480819/1000000000 : ℝ), (767985647/2000000000 : ℝ)] ![(8310150827657/25000000000000 : ℝ), (9204675199787/25000000000000 : ℝ), (29940695873831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172164583/10000000000 : ℝ)|^4963 ≤ (8310150827657/25000000000000 : ℝ)^3939
        have hw : |(4172164583/10000000000 : ℝ)|=(4172164583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(452480819/1000000000 : ℝ)|^4963 ≤ (9204675199787/25000000000000 : ℝ)^3939
        have hw : |(452480819/1000000000 : ℝ)|=(452480819/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(767985647/2000000000 : ℝ)|^4963 ≤ (29940695873831/100000000000000 : ℝ)^3939
        have hw : |(767985647/2000000000 : ℝ)|=(767985647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1661_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1073/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2667/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1631/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1073/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1073/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9901/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1073/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1073/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9901/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1073/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1073/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9901/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9901/100000 : ℝ) ^ (4959/1024 : ℝ) ≤ (1368677826720967/100000000000000000000 : ℝ) := by
    have hpowers : (9901/100000 : ℝ)^4959 ≤ (1368677826720967/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9901 : ℕ)^4959*100000000000000000000^1024 ≤ 1368677826720967^1024*100000^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9901 100000 1368677826720967 100000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9901/100000 : ℝ)) (X := (1368677826720967/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1073/6250 : ℝ) ^ (4959/1024 : ℝ) ≤ (3935055925309531/20000000000000000000 : ℝ) := by
    have hpowers : (1073/6250 : ℝ)^4959 ≤ (3935055925309531/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1073 : ℕ)^4959*20000000000000000000^1024 ≤ 3935055925309531^1024*6250^4959 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1073 6250 3935055925309531 20000000000000000000 4959 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1073/6250 : ℝ)) (X := (3935055925309531/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001368677826720967/50000000000000000000 : ℝ) ≤ (400002260957247/400000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (50001368677826720967/50000000000000000000 : ℝ)^1024 ≤ (400002260957247/400000000000000 : ℝ)^4959 := by
      have hnat : (50001368677826720967 : ℕ)^1024*400000000000000^4959 ≤ 400002260957247^4959*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001368677826720967 50000000000000000000 400002260957247 400000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400002260957247/400000000000000 : ℝ)) (X := (50001368677826720967/50000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010521978726634311/50000000000000000000 : ℝ) ≤ (10000434507228779/10000000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (50010521978726634311/50000000000000000000 : ℝ)^1024 ≤ (10000434507228779/10000000000000000 : ℝ)^4959 := by
      have hnat : (50010521978726634311 : ℕ)^1024*10000000000000000^4959 ≤ 10000434507228779^4959*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010521978726634311 50000000000000000000 10000434507228779 10000000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000434507228779/10000000000000000 : ℝ)) (X := (50010521978726634311/50000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10003935055925309531/10000000000000000000 : ℝ) ≤ (10000812490526383/10000000000000000 : ℝ) ^ (4959/1024 : ℝ) := by
    have hpowers : (10003935055925309531/10000000000000000000 : ℝ)^1024 ≤ (10000812490526383/10000000000000000 : ℝ)^4959 := by
      have hnat : (10003935055925309531 : ℕ)^1024*10000000000000000^4959 ≤ 10000812490526383^4959*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003935055925309531 10000000000000000000 10000812490526383 10000000000000000 1024 4959 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000812490526383/10000000000000000 : ℝ)) (X := (10003935055925309531/10000000000000000000 : ℝ)) (by norm_num) 4959 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1368677826720967/100000000000000000000 : ℝ) ≤ ((72662925934148694317/72670000000000000000 : ℝ)+2*(94495824401/181675000000000 : ℝ)*(9901/100000 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (72662925934148694317/72670000000000000000 : ℝ)+2*(94495824401/181675000000000 : ℝ)*(9901/100000 : ℝ)=(400002260957247/400000000000000 : ℝ) by norm_num, show 1+2*(1368677826720967/100000000000000000000 : ℝ)=(50001368677826720967/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3935055925309531/20000000000000000000 : ℝ)+(1368677826720967/100000000000000000000 : ℝ) ≤ ((72662925934148694317/72670000000000000000 : ℝ)+(94495824401/181675000000000 : ℝ)*((1073/6250 : ℝ)+(9901/100000 : ℝ)))^(4959/1024 : ℝ) := by
    rw [show (72662925934148694317/72670000000000000000 : ℝ)+(94495824401/181675000000000 : ℝ)*((1073/6250 : ℝ)+(9901/100000 : ℝ))=(10000434507228779/10000000000000000 : ℝ) by norm_num, show 1+(3935055925309531/20000000000000000000 : ℝ)+(1368677826720967/100000000000000000000 : ℝ)=(50010521978726634311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3935055925309531/20000000000000000000 : ℝ) ≤ ((72662925934148694317/72670000000000000000 : ℝ)+2*(94495824401/181675000000000 : ℝ)*(1073/6250 : ℝ))^(4959/1024 : ℝ) := by
    rw [show (72662925934148694317/72670000000000000000 : ℝ)+2*(94495824401/181675000000000 : ℝ)*(1073/6250 : ℝ)=(10000812490526383/10000000000000000 : ℝ) by norm_num, show 1+2*(3935055925309531/20000000000000000000 : ℝ)=(10003935055925309531/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (72662925934148694317/72670000000000000000 : ℝ)*(X 1 0+X 2 0)+(94495824401/181675000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (9901/100000 : ℝ)) (hi := (1073/6250 : ℝ)) (c := (72662925934148694317/72670000000000000000 : ℝ)) (alpha := (94495824401/181675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (72662925934148694317/72670000000000000000 : ℝ)*(X 0 1+X 2 1)+(94495824401/181675000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (9901/100000 : ℝ)) (hi := (1073/6250 : ℝ)) (c := (72662925934148694317/72670000000000000000 : ℝ)) (alpha := (94495824401/181675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (72662925934148694317/72670000000000000000 : ℝ)*(X 0 2+X 1 2)+(94495824401/181675000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4959/1024 : ℝ)) (lo := (9901/100000 : ℝ)) (hi := (1073/6250 : ℝ)) (c := (72662925934148694317/72670000000000000000 : ℝ)) (alpha := (94495824401/181675000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-791636487/5000000000 : ℝ)*X 0 0+(5447247309/10000000000 : ℝ)*X 0 1+(2591007303/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346874777/10000000000 : ℝ)*X 1 0+(-1719834833/10000000000 : ℝ)*X 1 1+(207280571/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346873173/10000000000 : ℝ)*X 2 0+(2591007679/5000000000 : ℝ)*X 2 1+(-214979443/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1042996983/2500000000 : ℝ)*X 0 0+(383447089/1000000000 : ℝ)*X 0 1+(3624167/8000000 : ℝ)*X 0 2+(1042996983/2500000000 : ℝ)*X 1 0+(383447089/1000000000 : ℝ)*X 1 1+(3624167/8000000 : ℝ)*X 1 2+(1042996983/2500000000 : ℝ)*X 2 0+(383447089/1000000000 : ℝ)*X 2 1+(3624167/8000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1583339209/10000000000 : ℝ)*X 0 0+(518407403/1000000000 : ℝ)*X 0 1+(5445166189/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5275926523/10000000000 : ℝ)*X 1 0+(-1456684673/10000000000 : ℝ)*X 1 1+(5445165257/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055185461/2000000000 : ℝ)*X 2 0+(5445164849/10000000000 : ℝ)*X 2 1+(-291336831/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4172164583/10000000000 : ℝ)*X 0 0+(452480819/1000000000 : ℝ)*X 0 1+(767985647/2000000000 : ℝ)*X 0 2+(4172164583/10000000000 : ℝ)*X 1 0+(452480819/1000000000 : ℝ)*X 1 1+(767985647/2000000000 : ℝ)*X 1 2+(4172164583/10000000000 : ℝ)*X 2 0+(452480819/1000000000 : ℝ)*X 2 1+(767985647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1661_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23344809734068063542033322179/1816750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348154673/20000000000000 : ℝ)*(base19) + (68308457/12500000000000 : ℝ)*(base23) + (105282973/50000000000000 : ℝ)*(upper3) + (2940847/10000000000000 : ℝ)*(lower4) + (1301914067796629/50000000000000 : ℝ)*(major0) + (1301914067796629/50000000000000 : ℝ)*(major1) + (1301914067796629/50000000000000 : ℝ)*(major2) + (942575861424487/25000000000000 : ℝ)*(sp0) + (3770320832246299/100000000000000 : ℝ)*(sp1) + (94257827856169/2500000000000 : ℝ)*(sp2) + (179666034960181/12500000000000 : ℝ)*(sp3) + (19127321717/100000000000000 : ℝ)*(sp4) + (278509539/3125000000000 : ℝ)*(sp6) + (2495079957/50000000000000 : ℝ)*(sp7) + (718666634920681/50000000000000 : ℝ)*(f.failure) + (235645160813729/6250000000000 : ℝ)*(f.sum) + (87234549521177/36335000000000000000000000000 : ℝ)*base65 + (10299129404101342607/3633500000000000000000000000000000 : ℝ)*base68 + (8552945494962842607/3633500000000000000000000000000000 : ℝ)*base70 + (31506337756882157393/3633500000000000000000000000000000 : ℝ)*base71 + (43198014895977/36335000000000000000000000000 : ℝ)*base73 + (558748519366842607/3633500000000000000000000000000000 : ℝ)*base76 + (1883586216517342607/3633500000000000000000000000000000 : ℝ)*base78 + (35246661599533657393/3633500000000000000000000000000000 : ℝ)*base79 + (30576521229491/18167500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (6361679/2500000000000000000000 : ℝ)*base90 + (6361679/2500000000000000000000 : ℝ)*base92 + (6361679/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3837920392012650976666405659/908375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (504784111/100000000000000 : ℝ)*(base19) + (4678433/1562500000000 : ℝ)*(base23) + (20393041/5000000000000 : ℝ)*(lower2) + (6306023/10000000000000 : ℝ)*(lower3) + (108501413/100000000000000 : ℝ)*(lower5) + (1322547844489109/50000000000000 : ℝ)*(major0) + (1322547844489109/50000000000000 : ℝ)*(major1) + (1322547844489109/50000000000000 : ℝ)*(major2) + (1215691261/50000000000000 : ℝ)*(sp0) + (128366731/100000000000000 : ℝ)*(sp3) + (478759440906311/12500000000000 : ℝ)*(sp4) + (1915038726924449/50000000000000 : ℝ)*(sp5) + (3830077659213297/100000000000000 : ℝ)*(sp6) + (91257071882627/6250000000000 : ℝ)*(sp7) + (1460113278488763/100000000000000 : ℝ)*(f.failure) + (383007795863301/10000000000000 : ℝ)*(f.sum) + (3287559728151/4541875000000000000000000000 : ℝ)*base66 + (41913637120407706447/3633500000000000000000000000000000 : ℝ)*base68 + (11085110903828706447/3633500000000000000000000000000000 : ℝ)*base70 + (1986711605606706447/3633500000000000000000000000000000 : ℝ)*base72 + (43774200165547/9083750000000000000000000000 : ℝ)*base74 + (22526530855465706447/3633500000000000000000000000000000 : ℝ)*base76 + (34938388730395206447/3633500000000000000000000000000000 : ℝ)*base78 + (17828234658889793553/3633500000000000000000000000000000 : ℝ)*base79 + (33110073783447/36335000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (88558483/5000000000000000000000 : ℝ)*base89 + (88558483/5000000000000000000000 : ℝ)*base91 + (88558483/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1661_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1073/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9901/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2667/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1661_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1661_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2667/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1661_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1661_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1661_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4959/1024 : ℝ) ≤ p) (hpb : p ≤ (4963/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (90578441/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2667/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1631/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1661_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
