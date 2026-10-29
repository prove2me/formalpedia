-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1560_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:24:33.881368+00:00
-- url     : https://prove2.me/submissions/00d4cbc4-6fc8-4848-9cde-d2d11b2e50cb

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
theorem support_rectangle_w1560_s0_0 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1636087001/10000000000 : ℝ)*x 0 + (2938407721/5000000000 : ℝ)*x 1 + (2437658909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1636087001/10000000000 : ℝ)^4617 ≤ (1220821934089/12500000000000 : ℝ)^3593 := by
    have hnat : (1636087001 : ℕ)^4617*12500000000000^3593 ≤ 1220821934089^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636087001 10000000000 1220821934089 12500000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2938407721/5000000000 : ℝ)^4617 ≤ (50506567971993/100000000000000 : ℝ)^3593 := by
    have hnat : (2938407721 : ℕ)^4617*100000000000000^3593 ≤ 50506567971993^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2938407721 5000000000 50506567971993 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2437658909/5000000000 : ℝ)^4617 ≤ (158907426181/400000000000 : ℝ)^3593 := by
    have hnat : (2437658909 : ℕ)^4617*400000000000^3593 ≤ 158907426181^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2437658909 5000000000 158907426181 400000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1636087001/10000000000 : ℝ), (2938407721/5000000000 : ℝ), (2437658909/5000000000 : ℝ)] ![(1220821934089/12500000000000 : ℝ), (50506567971993/100000000000000 : ℝ), (158907426181/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1636087001/10000000000 : ℝ)|^4617 ≤ (1220821934089/12500000000000 : ℝ)^3593
        have hw : |(-1636087001/10000000000 : ℝ)|=(1636087001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2938407721/5000000000 : ℝ)|^4617 ≤ (50506567971993/100000000000000 : ℝ)^3593
        have hw : |(2938407721/5000000000 : ℝ)|=(2938407721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2437658909/5000000000 : ℝ)|^4617 ≤ (158907426181/400000000000 : ℝ)^3593
        have hw : |(2437658909/5000000000 : ℝ)|=(2437658909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s0_1 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5467615691/10000000000 : ℝ)*x 0 + (-438815383/2000000000 : ℝ)*x 1 + (243765891/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5467615691/10000000000 : ℝ)^4617 ≤ (9206631621107/20000000000000 : ℝ)^3593 := by
    have hnat : (5467615691 : ℕ)^4617*20000000000000^3593 ≤ 9206631621107^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467615691 10000000000 9206631621107 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438815383/2000000000 : ℝ)^4617 ≤ (14239985314487/100000000000000 : ℝ)^3593 := by
    have hnat : (438815383 : ℕ)^4617*100000000000000^3593 ≤ 14239985314487^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438815383 2000000000 14239985314487 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (243765891/500000000 : ℝ)^4617 ≤ (2482928535387/6250000000000 : ℝ)^3593 := by
    have hnat : (243765891 : ℕ)^4617*6250000000000^3593 ≤ 2482928535387^3593*500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243765891 500000000 2482928535387 6250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5467615691/10000000000 : ℝ), (-438815383/2000000000 : ℝ), (243765891/500000000 : ℝ)] ![(9206631621107/20000000000000 : ℝ), (14239985314487/100000000000000 : ℝ), (2482928535387/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5467615691/10000000000 : ℝ)|^4617 ≤ (9206631621107/20000000000000 : ℝ)^3593
        have hw : |(5467615691/10000000000 : ℝ)|=(5467615691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438815383/2000000000 : ℝ)|^4617 ≤ (14239985314487/100000000000000 : ℝ)^3593
        have hw : |(-438815383/2000000000 : ℝ)|=(438815383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(243765891/500000000 : ℝ)|^4617 ≤ (2482928535387/6250000000000 : ℝ)^3593
        have hw : |(243765891/500000000 : ℝ)|=(243765891/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s0_2 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (683451967/1250000000 : ℝ)*x 0 + (609414721/1250000000 : ℝ)*x 1 + (-2194076921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683451967/1250000000 : ℝ)^4617 ≤ (46033158592377/100000000000000 : ℝ)^3593 := by
    have hnat : (683451967 : ℕ)^4617*100000000000000^3593 ≤ 46033158592377^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683451967 1250000000 46033158592377 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609414721/1250000000 : ℝ)^4617 ≤ (7945371204341/20000000000000 : ℝ)^3593 := by
    have hnat : (609414721 : ℕ)^4617*20000000000000^3593 ≤ 7945371204341^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609414721 1250000000 7945371204341 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2194076921/10000000000 : ℝ)^4617 ≤ (7119992682263/50000000000000 : ℝ)^3593 := by
    have hnat : (2194076921 : ℕ)^4617*50000000000000^3593 ≤ 7119992682263^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194076921 10000000000 7119992682263 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(683451967/1250000000 : ℝ), (609414721/1250000000 : ℝ), (-2194076921/10000000000 : ℝ)] ![(46033158592377/100000000000000 : ℝ), (7945371204341/20000000000000 : ℝ), (7119992682263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(683451967/1250000000 : ℝ)|^4617 ≤ (46033158592377/100000000000000 : ℝ)^3593
        have hw : |(683451967/1250000000 : ℝ)|=(683451967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(609414721/1250000000 : ℝ)|^4617 ≤ (7945371204341/20000000000000 : ℝ)^3593
        have hw : |(609414721/1250000000 : ℝ)|=(609414721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2194076921/10000000000 : ℝ)|^4617 ≤ (7119992682263/50000000000000 : ℝ)^3593
        have hw : |(-2194076921/10000000000 : ℝ)|=(2194076921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s0_3 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4132440309/10000000000 : ℝ)*x 0 + (3092641137/10000000000 : ℝ)*x 1 + (2720320923/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4132440309/10000000000 : ℝ)^4617 ≤ (803093313071/2500000000000 : ℝ)^3593 := by
    have hnat : (4132440309 : ℕ)^4617*2500000000000^3593 ≤ 803093313071^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132440309 10000000000 803093313071 2500000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3092641137/10000000000 : ℝ)^4617 ≤ (22134726148039/100000000000000 : ℝ)^3593 := by
    have hnat : (3092641137 : ℕ)^4617*100000000000000^3593 ≤ 22134726148039^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3092641137 10000000000 22134726148039 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2720320923/5000000000 : ℝ)^4617 ≤ (22870770657319/50000000000000 : ℝ)^3593 := by
    have hnat : (2720320923 : ℕ)^4617*50000000000000^3593 ≤ 22870770657319^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720320923 5000000000 22870770657319 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4132440309/10000000000 : ℝ), (3092641137/10000000000 : ℝ), (2720320923/5000000000 : ℝ)] ![(803093313071/2500000000000 : ℝ), (22134726148039/100000000000000 : ℝ), (22870770657319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4132440309/10000000000 : ℝ)|^4617 ≤ (803093313071/2500000000000 : ℝ)^3593
        have hw : |(4132440309/10000000000 : ℝ)|=(4132440309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3092641137/10000000000 : ℝ)|^4617 ≤ (22134726148039/100000000000000 : ℝ)^3593
        have hw : |(3092641137/10000000000 : ℝ)|=(3092641137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2720320923/5000000000 : ℝ)|^4617 ≤ (22870770657319/50000000000000 : ℝ)^3593
        have hw : |(2720320923/5000000000 : ℝ)|=(2720320923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s0_4 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-204902193/1250000000 : ℝ)*x 0 + (4900613391/10000000000 : ℝ)*x 1 + (2925311061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204902193/1250000000 : ℝ)^4617 ≤ (9790595671271/100000000000000 : ℝ)^3593 := by
    have hnat : (204902193 : ℕ)^4617*100000000000000^3593 ≤ 9790595671271^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204902193 1250000000 9790595671271 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4900613391/10000000000 : ℝ)^4617 ≤ (19995959749429/50000000000000 : ℝ)^3593 := by
    have hnat : (4900613391 : ℕ)^4617*50000000000000^3593 ≤ 19995959749429^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4900613391 10000000000 19995959749429 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2925311061/5000000000 : ℝ)^4617 ≤ (12554371202199/25000000000000 : ℝ)^3593 := by
    have hnat : (2925311061 : ℕ)^4617*25000000000000^3593 ≤ 12554371202199^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2925311061 5000000000 12554371202199 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204902193/1250000000 : ℝ), (4900613391/10000000000 : ℝ), (2925311061/5000000000 : ℝ)] ![(9790595671271/100000000000000 : ℝ), (19995959749429/50000000000000 : ℝ), (12554371202199/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204902193/1250000000 : ℝ)|^4617 ≤ (9790595671271/100000000000000 : ℝ)^3593
        have hw : |(-204902193/1250000000 : ℝ)|=(204902193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4900613391/10000000000 : ℝ)|^4617 ≤ (19995959749429/50000000000000 : ℝ)^3593
        have hw : |(4900613391/10000000000 : ℝ)|=(4900613391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2925311061/5000000000 : ℝ)|^4617 ≤ (12554371202199/25000000000000 : ℝ)^3593
        have hw : |(2925311061/5000000000 : ℝ)|=(2925311061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s0_5 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649230959/1250000000 : ℝ)*x 0 + (-121877291/1000000000 : ℝ)*x 1 + (365663881/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649230959/1250000000 : ℝ)^4617 ≤ (21546366004841/50000000000000 : ℝ)^3593 := by
    have hnat : (649230959 : ℕ)^4617*50000000000000^3593 ≤ 21546366004841^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649230959 1250000000 21546366004841 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (121877291/1000000000 : ℝ)^4617 ≤ (6689783458993/100000000000000 : ℝ)^3593 := by
    have hnat : (121877291 : ℕ)^4617*100000000000000^3593 ≤ 6689783458993^3593*1000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121877291 1000000000 6689783458993 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365663881/625000000 : ℝ)^4617 ≤ (50217484522029/100000000000000 : ℝ)^3593 := by
    have hnat : (365663881 : ℕ)^4617*100000000000000^3593 ≤ 50217484522029^3593*625000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365663881 625000000 50217484522029 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649230959/1250000000 : ℝ), (-121877291/1000000000 : ℝ), (365663881/625000000 : ℝ)] ![(21546366004841/50000000000000 : ℝ), (6689783458993/100000000000000 : ℝ), (50217484522029/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649230959/1250000000 : ℝ)|^4617 ≤ (21546366004841/50000000000000 : ℝ)^3593
        have hw : |(649230959/1250000000 : ℝ)|=(649230959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-121877291/1000000000 : ℝ)|^4617 ≤ (6689783458993/100000000000000 : ℝ)^3593
        have hw : |(-121877291/1000000000 : ℝ)|=(121877291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(365663881/625000000 : ℝ)|^4617 ≤ (50217484522029/100000000000000 : ℝ)^3593
        have hw : |(365663881/625000000 : ℝ)|=(365663881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s0_6 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649230967/1250000000 : ℝ)*x 0 + (5850622247/10000000000 : ℝ)*x 1 + (-38086643/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649230967/1250000000 : ℝ)^4617 ≤ (43092732692017/100000000000000 : ℝ)^3593 := by
    have hnat : (649230967 : ℕ)^4617*100000000000000^3593 ≤ 43092732692017^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649230967 1250000000 43092732692017 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5850622247/10000000000 : ℝ)^4617 ≤ (50217486187483/100000000000000 : ℝ)^3593 := by
    have hnat : (5850622247 : ℕ)^4617*100000000000000^3593 ≤ 50217486187483^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5850622247 10000000000 50217486187483 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38086643/312500000 : ℝ)^4617 ≤ (6689781103193/100000000000000 : ℝ)^3593 := by
    have hnat : (38086643 : ℕ)^4617*100000000000000^3593 ≤ 6689781103193^3593*312500000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38086643 312500000 6689781103193 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649230967/1250000000 : ℝ), (5850622247/10000000000 : ℝ), (-38086643/312500000 : ℝ)] ![(43092732692017/100000000000000 : ℝ), (50217486187483/100000000000000 : ℝ), (6689781103193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649230967/1250000000 : ℝ)|^4617 ≤ (43092732692017/100000000000000 : ℝ)^3593
        have hw : |(649230967/1250000000 : ℝ)|=(649230967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5850622247/10000000000 : ℝ)|^4617 ≤ (50217486187483/100000000000000 : ℝ)^3593
        have hw : |(5850622247/10000000000 : ℝ)|=(5850622247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38086643/312500000 : ℝ)|^4617 ≤ (6689781103193/100000000000000 : ℝ)^3593
        have hw : |(-38086643/312500000 : ℝ)|=(38086643/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s0_7 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1034944791/2500000000 : ℝ)*x 0 + (215253467/400000000 : ℝ)*x 1 + (315405089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034944791/2500000000 : ℝ)^4617 ≤ (4024632362353/12500000000000 : ℝ)^3593 := by
    have hnat : (1034944791 : ℕ)^4617*12500000000000^3593 ≤ 4024632362353^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034944791 2500000000 4024632362353 12500000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215253467/400000000 : ℝ)^4617 ≤ (45101837412979/100000000000000 : ℝ)^3593 := by
    have hnat : (215253467 : ℕ)^4617*100000000000000^3593 ≤ 45101837412979^3593*400000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215253467 400000000 45101837412979 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315405089/1000000000 : ℝ)^4617 ≤ (11350551838263/50000000000000 : ℝ)^3593 := by
    have hnat : (315405089 : ℕ)^4617*50000000000000^3593 ≤ 11350551838263^3593*1000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315405089 1000000000 11350551838263 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1034944791/2500000000 : ℝ), (215253467/400000000 : ℝ), (315405089/1000000000 : ℝ)] ![(4024632362353/12500000000000 : ℝ), (45101837412979/100000000000000 : ℝ), (11350551838263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1034944791/2500000000 : ℝ)|^4617 ≤ (4024632362353/12500000000000 : ℝ)^3593
        have hw : |(1034944791/2500000000 : ℝ)|=(1034944791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215253467/400000000 : ℝ)|^4617 ≤ (45101837412979/100000000000000 : ℝ)^3593
        have hw : |(215253467/400000000 : ℝ)|=(215253467/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(315405089/1000000000 : ℝ)|^4617 ≤ (11350551838263/50000000000000 : ℝ)^3593
        have hw : |(315405089/1000000000 : ℝ)|=(315405089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1560_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (137/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24877/100000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4615/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4615 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4615*1^1024 ≤ 0^1024*1^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4615/1024 : ℝ) ≤ (1608976377429494689/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4615 ≤ (1608976377429494689/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4615*100000000000000000000^1024 ≤ 1608976377429494689^1024*5^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1608976377429494689 100000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1608976377429494689/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4615 := by
      have hnat : (1 : ℕ)^1024*1^4615 ≤ 1^4615*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101608976377429494689/100000000000000000000 : ℝ) ≤ (100354794239703/100000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (101608976377429494689/100000000000000000000 : ℝ)^1024 ≤ (100354794239703/100000000000000 : ℝ)^4615 := by
      have hnat : (101608976377429494689 : ℕ)^1024*100000000000000^4615 ≤ 100354794239703^4615*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101608976377429494689 100000000000000000000 100354794239703 100000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100354794239703/100000000000000 : ℝ)) (X := (101608976377429494689/100000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51608976377429494689/50000000000000000000 : ℝ) ≤ (50354794239703/50000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (51608976377429494689/50000000000000000000 : ℝ)^1024 ≤ (50354794239703/50000000000000 : ℝ)^4615 := by
      have hnat : (51608976377429494689 : ℕ)^1024*50000000000000^4615 ≤ 50354794239703^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51608976377429494689 50000000000000000000 50354794239703 50000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (50354794239703/50000000000000 : ℝ)) (X := (51608976377429494689/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(354794239703/40000000000000 : ℝ)*(0 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(354794239703/40000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1608976377429494689/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(354794239703/40000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4615/1024 : ℝ) := by
    rw [show (1 : ℝ)+(354794239703/40000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(100354794239703/100000000000000 : ℝ) by norm_num, show 1+(1608976377429494689/100000000000000000000 : ℝ)+(0 : ℝ)=(101608976377429494689/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1608976377429494689/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(354794239703/40000000000000 : ℝ)*(2/5 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(354794239703/40000000000000 : ℝ)*(2/5 : ℝ)=(50354794239703/50000000000000 : ℝ) by norm_num, show 1+2*(1608976377429494689/100000000000000000000 : ℝ)=(51608976377429494689/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(354794239703/40000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (354794239703/40000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(354794239703/40000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (354794239703/40000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(354794239703/40000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (354794239703/40000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1636087001/10000000000 : ℝ)*X 0 0+(2938407721/5000000000 : ℝ)*X 0 1+(2437658909/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5467615691/10000000000 : ℝ)*X 1 0+(-438815383/2000000000 : ℝ)*X 1 1+(243765891/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((683451967/1250000000 : ℝ)*X 2 0+(609414721/1250000000 : ℝ)*X 2 1+(-2194076921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4132440309/10000000000 : ℝ)*X 0 0+(3092641137/10000000000 : ℝ)*X 0 1+(2720320923/5000000000 : ℝ)*X 0 2+(4132440309/10000000000 : ℝ)*X 1 0+(3092641137/10000000000 : ℝ)*X 1 1+(2720320923/5000000000 : ℝ)*X 1 2+(4132440309/10000000000 : ℝ)*X 2 0+(3092641137/10000000000 : ℝ)*X 2 1+(2720320923/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-204902193/1250000000 : ℝ)*X 0 0+(4900613391/10000000000 : ℝ)*X 0 1+(2925311061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((649230959/1250000000 : ℝ)*X 1 0+(-121877291/1000000000 : ℝ)*X 1 1+(365663881/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((649230967/1250000000 : ℝ)*X 2 0+(5850622247/10000000000 : ℝ)*X 2 1+(-38086643/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1034944791/2500000000 : ℝ)*X 0 0+(215253467/400000000 : ℝ)*X 0 1+(315405089/1000000000 : ℝ)*X 0 2+(1034944791/2500000000 : ℝ)*X 1 0+(215253467/400000000 : ℝ)*X 1 1+(315405089/1000000000 : ℝ)*X 1 2+(1034944791/2500000000 : ℝ)*X 2 0+(215253467/400000000 : ℝ)*X 2 1+(315405089/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1021136971217746106829/200000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6109609/12500000000000 : ℝ)*(base1) + (532938011/50000000000000 : ℝ)*(base19) + (1074094047/100000000000000 : ℝ)*(base23) + (861901/625000000000 : ℝ)*(upper3) + (138276177/100000000000000 : ℝ)*(upper5) + (356102495103119/50000000000000 : ℝ)*(major0) + (356102495103119/50000000000000 : ℝ)*(major1) + (356102495103119/50000000000000 : ℝ)*(major2) + (998508343578891/100000000000000 : ℝ)*(sp0) + (249627793293861/25000000000000 : ℝ)*(sp1) + (998511164957419/100000000000000 : ℝ)*(sp2) + (425895840950987/100000000000000 : ℝ)*(sp3) + (3944349447/100000000000000 : ℝ)*(sp4) + (420335913/25000000000000 : ℝ)*(sp7) + (425897571171511/100000000000000 : ℝ)*(f.failure) + (499256119525733/50000000000000 : ℝ)*(f.sum) + (1312981081657/1000000000000000000000000000 : ℝ)*base65 + (231148902343/2000000000000000000000000000 : ℝ)*base68 + (14403591625657/2000000000000000000000000000 : ℝ)*base69 + (1274801503657/2000000000000000000000000000 : ℝ)*base71 + (1928474874657/1000000000000000000000000000 : ℝ)*base73 + (7559660209657/2000000000000000000000000000 : ℝ)*base75 + (1306694343657/2000000000000000000000000000 : ℝ)*base77 + (5991968711657/2000000000000000000000000000 : ℝ)*base79 + (7068163550657/1000000000000000000000000000 : ℝ)*base81 + (12276871/5000000000000000000000 : ℝ)*base90 + (12276871/5000000000000000000000 : ℝ)*base92 + (12276871/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (235917508220032067157/62500000000000000000000000 : ℝ) := by norm_num
    linear_combination (90277583/12500000000000 : ℝ)*(base19) + (400827209/50000000000000 : ℝ)*(base23) + (52683601/100000000000000 : ℝ)*(base39) + (1346671/1250000000000 : ℝ)*(upper3) + (125437353/100000000000000 : ℝ)*(upper5) + (93849915648193/12500000000000 : ℝ)*(major0) + (93849915648193/12500000000000 : ℝ)*(major1) + (93849909062743/12500000000000 : ℝ)*(major2) + (1939970481/100000000000000 : ℝ)*(sp1) + (1109229943/50000000000000 : ℝ)*(sp2) + (52631077163427/5000000000000 : ℝ)*(sp4) + (526309440538697/50000000000000 : ℝ)*(sp5) + (263154643959459/25000000000000 : ℝ)*(sp6) + (448976928596269/100000000000000 : ℝ)*(sp7) + (448976928596269/100000000000000 : ℝ)*(f.failure) + (52631079797607/5000000000000 : ℝ)*(f.sum) + (94791601751/62500000000000000000000000 : ℝ)*base65 + (756566327829/500000000000000000000000000 : ℝ)*base67 + (2817475161679/500000000000000000000000000 : ℝ)*base69 + (1669267057829/500000000000000000000000000 : ℝ)*base71 + (296626004001/62500000000000000000000000 : ℝ)*base73 + (6014911479679/500000000000000000000000000 : ℝ)*base75 + (635638552679/500000000000000000000000000 : ℝ)*base77 + (2110432049179/500000000000000000000000000 : ℝ)*base79 + (839547589679/250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (21863709/5000000000000000000000 : ℝ)*base90 + (21863709/5000000000000000000000 : ℝ)*base92 + (71863709/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1560_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (137/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24877/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1560_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1560_s1_0 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1777232153/10000000000 : ℝ)*x 0 + (221623417/400000000 : ℝ)*x 1 + (640077547/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1777232153/10000000000 : ℝ)^4617 ≤ (10862312473331/100000000000000 : ℝ)^3593 := by
    have hnat : (1777232153 : ℕ)^4617*100000000000000^3593 ≤ 10862312473331^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1777232153 10000000000 10862312473331 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221623417/400000000 : ℝ)^4617 ≤ (4682409301741/10000000000000 : ℝ)^3593 := by
    have hnat : (221623417 : ℕ)^4617*10000000000000^3593 ≤ 4682409301741^3593*400000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221623417 400000000 4682409301741 10000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (640077547/1250000000 : ℝ)^4617 ≤ (21156797251793/50000000000000 : ℝ)^3593 := by
    have hnat : (640077547 : ℕ)^4617*50000000000000^3593 ≤ 21156797251793^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      640077547 1250000000 21156797251793 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1777232153/10000000000 : ℝ), (221623417/400000000 : ℝ), (640077547/1250000000 : ℝ)] ![(10862312473331/100000000000000 : ℝ), (4682409301741/10000000000000 : ℝ), (21156797251793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1777232153/10000000000 : ℝ)|^4617 ≤ (10862312473331/100000000000000 : ℝ)^3593
        have hw : |(-1777232153/10000000000 : ℝ)|=(1777232153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221623417/400000000 : ℝ)|^4617 ≤ (4682409301741/10000000000000 : ℝ)^3593
        have hw : |(221623417/400000000 : ℝ)|=(221623417/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(640077547/1250000000 : ℝ)|^4617 ≤ (21156797251793/50000000000000 : ℝ)^3593
        have hw : |(640077547/1250000000 : ℝ)|=(640077547/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s1_1 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5378138413/10000000000 : ℝ)*x 0 + (-249642221/1250000000 : ℝ)*x 1 + (1280155087/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378138413/10000000000 : ℝ)^4617 ≤ (45067395760603/100000000000000 : ℝ)^3593 := by
    have hnat : (5378138413 : ℕ)^4617*100000000000000^3593 ≤ 45067395760603^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378138413 10000000000 45067395760603 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249642221/1250000000 : ℝ)^4617 ≤ (3154752505823/25000000000000 : ℝ)^3593 := by
    have hnat : (249642221 : ℕ)^4617*25000000000000^3593 ≤ 3154752505823^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249642221 1250000000 3154752505823 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1280155087/2500000000 : ℝ)^4617 ≤ (4231359420627/10000000000000 : ℝ)^3593 := by
    have hnat : (1280155087 : ℕ)^4617*10000000000000^3593 ≤ 4231359420627^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280155087 2500000000 4231359420627 10000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378138413/10000000000 : ℝ), (-249642221/1250000000 : ℝ), (1280155087/2500000000 : ℝ)] ![(45067395760603/100000000000000 : ℝ), (3154752505823/25000000000000 : ℝ), (4231359420627/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378138413/10000000000 : ℝ)|^4617 ≤ (45067395760603/100000000000000 : ℝ)^3593
        have hw : |(5378138413/10000000000 : ℝ)|=(5378138413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-249642221/1250000000 : ℝ)|^4617 ≤ (3154752505823/25000000000000 : ℝ)^3593
        have hw : |(-249642221/1250000000 : ℝ)|=(249642221/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1280155087/2500000000 : ℝ)|^4617 ≤ (4231359420627/10000000000000 : ℝ)^3593
        have hw : |(1280155087/2500000000 : ℝ)|=(1280155087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s1_2 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075627673/2000000000 : ℝ)*x 0 + (5120620667/10000000000 : ℝ)*x 1 + (-998568707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075627673/2000000000 : ℝ)^4617 ≤ (45067395243741/100000000000000 : ℝ)^3593 := by
    have hnat : (1075627673 : ℕ)^4617*100000000000000^3593 ≤ 45067395243741^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075627673 2000000000 45067395243741 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5120620667/10000000000 : ℝ)^4617 ≤ (42313597593547/100000000000000 : ℝ)^3593 := by
    have hnat : (5120620667 : ℕ)^4617*100000000000000^3593 ≤ 42313597593547^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5120620667 10000000000 42313597593547 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (998568707/5000000000 : ℝ)^4617 ≤ (12619007149051/100000000000000 : ℝ)^3593 := by
    have hnat : (998568707 : ℕ)^4617*100000000000000^3593 ≤ 12619007149051^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      998568707 5000000000 12619007149051 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075627673/2000000000 : ℝ), (5120620667/10000000000 : ℝ), (-998568707/5000000000 : ℝ)] ![(45067395243741/100000000000000 : ℝ), (42313597593547/100000000000000 : ℝ), (12619007149051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075627673/2000000000 : ℝ)|^4617 ≤ (45067395243741/100000000000000 : ℝ)^3593
        have hw : |(1075627673/2000000000 : ℝ)|=(1075627673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5120620667/10000000000 : ℝ)|^4617 ≤ (42313597593547/100000000000000 : ℝ)^3593
        have hw : |(5120620667/10000000000 : ℝ)|=(5120620667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-998568707/5000000000 : ℝ)|^4617 ≤ (12619007149051/100000000000000 : ℝ)^3593
        have hw : |(-998568707/5000000000 : ℝ)|=(998568707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s1_3 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (169284081/400000000 : ℝ)*x 0 + (188153209/500000000 : ℝ)*x 1 + (2373834287/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169284081/400000000 : ℝ)^4617 ≤ (33122655319647/100000000000000 : ℝ)^3593 := by
    have hnat : (169284081 : ℕ)^4617*100000000000000^3593 ≤ 33122655319647^3593*400000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169284081 400000000 33122655319647 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188153209/500000000 : ℝ)^4617 ≤ (5696414391257/20000000000000 : ℝ)^3593 := by
    have hnat : (188153209 : ℕ)^4617*20000000000000^3593 ≤ 5696414391257^3593*500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188153209 500000000 5696414391257 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2373834287/5000000000 : ℝ)^4617 ≤ (38395272706011/100000000000000 : ℝ)^3593 := by
    have hnat : (2373834287 : ℕ)^4617*100000000000000^3593 ≤ 38395272706011^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2373834287 5000000000 38395272706011 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169284081/400000000 : ℝ), (188153209/500000000 : ℝ), (2373834287/5000000000 : ℝ)] ![(33122655319647/100000000000000 : ℝ), (5696414391257/20000000000000 : ℝ), (38395272706011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169284081/400000000 : ℝ)|^4617 ≤ (33122655319647/100000000000000 : ℝ)^3593
        have hw : |(169284081/400000000 : ℝ)|=(169284081/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(188153209/500000000 : ℝ)|^4617 ≤ (5696414391257/20000000000000 : ℝ)^3593
        have hw : |(188153209/500000000 : ℝ)|=(188153209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2373834287/5000000000 : ℝ)|^4617 ≤ (38395272706011/100000000000000 : ℝ)^3593
        have hw : |(2373834287/5000000000 : ℝ)|=(2373834287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s1_4 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-17774563/100000000 : ℝ)*x 0 + (5125011747/10000000000 : ℝ)*x 1 + (5536128461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17774563/100000000 : ℝ)^4617 ≤ (10864072914527/100000000000000 : ℝ)^3593 := by
    have hnat : (17774563 : ℕ)^4617*100000000000000^3593 ≤ 10864072914527^3593*100000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17774563 100000000 10864072914527 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125011747/10000000000 : ℝ)^4617 ≤ (2118011481647/5000000000000 : ℝ)^3593 := by
    have hnat : (5125011747 : ℕ)^4617*5000000000000^3593 ≤ 2118011481647^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125011747 10000000000 2118011481647 5000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5536128461/10000000000 : ℝ)^4617 ≤ (23387848718273/50000000000000 : ℝ)^3593 := by
    have hnat : (5536128461 : ℕ)^4617*50000000000000^3593 ≤ 23387848718273^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5536128461 10000000000 23387848718273 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-17774563/100000000 : ℝ), (5125011747/10000000000 : ℝ), (5536128461/10000000000 : ℝ)] ![(10864072914527/100000000000000 : ℝ), (2118011481647/5000000000000 : ℝ), (23387848718273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-17774563/100000000 : ℝ)|^4617 ≤ (10864072914527/100000000000000 : ℝ)^3593
        have hw : |(-17774563/100000000 : ℝ)|=(17774563/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125011747/10000000000 : ℝ)|^4617 ≤ (2118011481647/5000000000000 : ℝ)^3593
        have hw : |(5125011747/10000000000 : ℝ)|=(5125011747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5536128461/10000000000 : ℝ)|^4617 ≤ (23387848718273/50000000000000 : ℝ)^3593
        have hw : |(5536128461/10000000000 : ℝ)|=(5536128461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s1_5 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (658366187/1250000000 : ℝ)*x 0 + (-98852041/625000000 : ℝ)*x 1 + (2768063629/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (658366187/1250000000 : ℝ)^4617 ≤ (877468989121/2000000000000 : ℝ)^3593 := by
    have hnat : (658366187 : ℕ)^4617*2000000000000^3593 ≤ 877468989121^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658366187 1250000000 877468989121 2000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (98852041/625000000 : ℝ)^4617 ≤ (9350866149367/100000000000000 : ℝ)^3593 := by
    have hnat : (98852041 : ℕ)^4617*100000000000000^3593 ≤ 9350866149367^3593*625000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98852041 625000000 9350866149367 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2768063629/5000000000 : ℝ)^4617 ≤ (46775684375367/100000000000000 : ℝ)^3593 := by
    have hnat : (2768063629 : ℕ)^4617*100000000000000^3593 ≤ 46775684375367^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768063629 5000000000 46775684375367 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(658366187/1250000000 : ℝ), (-98852041/625000000 : ℝ), (2768063629/5000000000 : ℝ)] ![(877468989121/2000000000000 : ℝ), (9350866149367/100000000000000 : ℝ), (46775684375367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(658366187/1250000000 : ℝ)|^4617 ≤ (877468989121/2000000000000 : ℝ)^3593
        have hw : |(658366187/1250000000 : ℝ)|=(658366187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-98852041/625000000 : ℝ)|^4617 ≤ (9350866149367/100000000000000 : ℝ)^3593
        have hw : |(-98852041/625000000 : ℝ)|=(98852041/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2768063629/5000000000 : ℝ)|^4617 ≤ (46775684375367/100000000000000 : ℝ)^3593
        have hw : |(2768063629/5000000000 : ℝ)|=(2768063629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s1_6 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266931919/10000000000 : ℝ)*x 0 + (138403163/250000000 : ℝ)*x 1 + (-1581630297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266931919/10000000000 : ℝ)^4617 ≤ (43873475391893/100000000000000 : ℝ)^3593 := by
    have hnat : (5266931919 : ℕ)^4617*100000000000000^3593 ≤ 43873475391893^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266931919 10000000000 43873475391893 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (138403163/250000000 : ℝ)^4617 ≤ (23387838181387/50000000000000 : ℝ)^3593 := by
    have hnat : (138403163 : ℕ)^4617*50000000000000^3593 ≤ 23387838181387^3593*250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138403163 250000000 23387838181387 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1581630297/10000000000 : ℝ)^4617 ≤ (9350848227769/100000000000000 : ℝ)^3593 := by
    have hnat : (1581630297 : ℕ)^4617*100000000000000^3593 ≤ 9350848227769^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1581630297 10000000000 9350848227769 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266931919/10000000000 : ℝ), (138403163/250000000 : ℝ), (-1581630297/10000000000 : ℝ)] ![(43873475391893/100000000000000 : ℝ), (23387838181387/50000000000000 : ℝ), (9350848227769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266931919/10000000000 : ℝ)|^4617 ≤ (43873475391893/100000000000000 : ℝ)^3593
        have hw : |(5266931919/10000000000 : ℝ)|=(5266931919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(138403163/250000000 : ℝ)|^4617 ≤ (23387838181387/50000000000000 : ℝ)^3593
        have hw : |(138403163/250000000 : ℝ)|=(138403163/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1581630297/10000000000 : ℝ)|^4617 ≤ (9350848227769/100000000000000 : ℝ)^3593
        have hw : |(-1581630297/10000000000 : ℝ)|=(1581630297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s1_7 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132269637/312500000 : ℝ)*x 0 + (4737370707/10000000000 : ℝ)*x 1 + (1886757723/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132269637/312500000 : ℝ)^4617 ≤ (1656397452261/5000000000000 : ℝ)^3593 := by
    have hnat : (132269637 : ℕ)^4617*5000000000000^3593 ≤ 1656397452261^3593*312500000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132269637 312500000 1656397452261 5000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4737370707/10000000000 : ℝ)^4617 ≤ (478603626863/1250000000000 : ℝ)^3593 := by
    have hnat : (4737370707 : ℕ)^4617*1250000000000^3593 ≤ 478603626863^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4737370707 10000000000 478603626863 1250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1886757723/5000000000 : ℝ)^4617 ≤ (14291880392447/50000000000000 : ℝ)^3593 := by
    have hnat : (1886757723 : ℕ)^4617*50000000000000^3593 ≤ 14291880392447^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1886757723 5000000000 14291880392447 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132269637/312500000 : ℝ), (4737370707/10000000000 : ℝ), (1886757723/5000000000 : ℝ)] ![(1656397452261/5000000000000 : ℝ), (478603626863/1250000000000 : ℝ), (14291880392447/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132269637/312500000 : ℝ)|^4617 ≤ (1656397452261/5000000000000 : ℝ)^3593
        have hw : |(132269637/312500000 : ℝ)|=(132269637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4737370707/10000000000 : ℝ)|^4617 ≤ (478603626863/1250000000000 : ℝ)^3593
        have hw : |(4737370707/10000000000 : ℝ)|=(4737370707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1886757723/5000000000 : ℝ)|^4617 ≤ (14291880392447/50000000000000 : ℝ)^3593
        have hw : |(1886757723/5000000000 : ℝ)|=(1886757723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1560_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (137/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (1791/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2231/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24877/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (137/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24877/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (137/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24877/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (137/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24877/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (137/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24877/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (137/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24877/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (137/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (137/4000 : ℝ) ^ (4615/1024 : ℝ) ≤ (6221507531223/25000000000000000000 : ℝ) := by
    have hpowers : (137/4000 : ℝ)^4615 ≤ (6221507531223/25000000000000000000 : ℝ)^1024 := by
      have hnat : (137 : ℕ)^4615*25000000000000000000^1024 ≤ 6221507531223^1024*4000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        137 4000 6221507531223 25000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (137/4000 : ℝ)) (X := (6221507531223/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24877/100000 : ℝ) ^ (4615/1024 : ℝ) ≤ (94608628119398693/50000000000000000000 : ℝ) := by
    have hpowers : (24877/100000 : ℝ)^4615 ≤ (94608628119398693/50000000000000000000 : ℝ)^1024 := by
      have hnat : (24877 : ℕ)^4615*50000000000000000000^1024 ≤ 94608628119398693^1024*100000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24877 100000 94608628119398693 50000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24877/100000 : ℝ)) (X := (94608628119398693/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500006221507531223/12500000000000000000 : ℝ) ≤ (10000001104367927/10000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (12500006221507531223/12500000000000000000 : ℝ)^1024 ≤ (10000001104367927/10000000000000000 : ℝ)^4615 := by
      have hnat : (12500006221507531223 : ℕ)^1024*10000000000000000^4615 ≤ 10000001104367927^4615*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500006221507531223 12500000000000000000 10000001104367927 10000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001104367927/10000000000000000 : ℝ)) (X := (12500006221507531223/12500000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50094621071134461139/50000000000000000000 : ℝ) ≤ (10004195914149841/10000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50094621071134461139/50000000000000000000 : ℝ)^1024 ≤ (10004195914149841/10000000000000000 : ℝ)^4615 := by
      have hnat : (50094621071134461139 : ℕ)^1024*10000000000000000^4615 ≤ 10004195914149841^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50094621071134461139 50000000000000000000 10004195914149841 10000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004195914149841/10000000000000000 : ℝ)) (X := (50094621071134461139/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25094608628119398693/25000000000000000000 : ℝ) ≤ (2001678144786351/2000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (25094608628119398693/25000000000000000000 : ℝ)^1024 ≤ (2001678144786351/2000000000000000 : ℝ)^4615 := by
      have hnat : (25094608628119398693 : ℕ)^1024*2000000000000000^4615 ≤ 2001678144786351^4615*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25094608628119398693 25000000000000000000 2001678144786351 2000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001678144786351/2000000000000000 : ℝ)) (X := (25094608628119398693/25000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6221507531223/25000000000000000000 : ℝ) ≤ ((6702852788871708097/6703750000000000000 : ℝ)+2*(2097404890957/1072600000000000 : ℝ)*(137/4000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (6702852788871708097/6703750000000000000 : ℝ)+2*(2097404890957/1072600000000000 : ℝ)*(137/4000 : ℝ)=(10000001104367927/10000000000000000 : ℝ) by norm_num, show 1+2*(6221507531223/25000000000000000000 : ℝ)=(12500006221507531223/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(94608628119398693/50000000000000000000 : ℝ)+(6221507531223/25000000000000000000 : ℝ) ≤ ((6702852788871708097/6703750000000000000 : ℝ)+(2097404890957/1072600000000000 : ℝ)*((24877/100000 : ℝ)+(137/4000 : ℝ)))^(4615/1024 : ℝ) := by
    rw [show (6702852788871708097/6703750000000000000 : ℝ)+(2097404890957/1072600000000000 : ℝ)*((24877/100000 : ℝ)+(137/4000 : ℝ))=(10004195914149841/10000000000000000 : ℝ) by norm_num, show 1+(94608628119398693/50000000000000000000 : ℝ)+(6221507531223/25000000000000000000 : ℝ)=(50094621071134461139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(94608628119398693/50000000000000000000 : ℝ) ≤ ((6702852788871708097/6703750000000000000 : ℝ)+2*(2097404890957/1072600000000000 : ℝ)*(24877/100000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (6702852788871708097/6703750000000000000 : ℝ)+2*(2097404890957/1072600000000000 : ℝ)*(24877/100000 : ℝ)=(2001678144786351/2000000000000000 : ℝ) by norm_num, show 1+2*(94608628119398693/50000000000000000000 : ℝ)=(25094608628119398693/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6702852788871708097/6703750000000000000 : ℝ)*(X 1 0+X 2 0)+(2097404890957/1072600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (137/4000 : ℝ)) (hi := (24877/100000 : ℝ)) (c := (6702852788871708097/6703750000000000000 : ℝ)) (alpha := (2097404890957/1072600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6702852788871708097/6703750000000000000 : ℝ)*(X 0 1+X 2 1)+(2097404890957/1072600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (137/4000 : ℝ)) (hi := (24877/100000 : ℝ)) (c := (6702852788871708097/6703750000000000000 : ℝ)) (alpha := (2097404890957/1072600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6702852788871708097/6703750000000000000 : ℝ)*(X 0 2+X 1 2)+(2097404890957/1072600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (137/4000 : ℝ)) (hi := (24877/100000 : ℝ)) (c := (6702852788871708097/6703750000000000000 : ℝ)) (alpha := (2097404890957/1072600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1777232153/10000000000 : ℝ)*X 0 0+(221623417/400000000 : ℝ)*X 0 1+(640077547/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378138413/10000000000 : ℝ)*X 1 0+(-249642221/1250000000 : ℝ)*X 1 1+(1280155087/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1075627673/2000000000 : ℝ)*X 2 0+(5120620667/10000000000 : ℝ)*X 2 1+(-998568707/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((169284081/400000000 : ℝ)*X 0 0+(188153209/500000000 : ℝ)*X 0 1+(2373834287/5000000000 : ℝ)*X 0 2+(169284081/400000000 : ℝ)*X 1 0+(188153209/500000000 : ℝ)*X 1 1+(2373834287/5000000000 : ℝ)*X 1 2+(169284081/400000000 : ℝ)*X 2 0+(188153209/500000000 : ℝ)*X 2 1+(2373834287/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-17774563/100000000 : ℝ)*X 0 0+(5125011747/10000000000 : ℝ)*X 0 1+(5536128461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((658366187/1250000000 : ℝ)*X 1 0+(-98852041/625000000 : ℝ)*X 1 1+(2768063629/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266931919/10000000000 : ℝ)*X 2 0+(138403163/250000000 : ℝ)*X 2 1+(-1581630297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((132269637/312500000 : ℝ)*X 0 0+(4737370707/10000000000 : ℝ)*X 0 1+(1886757723/5000000000 : ℝ)*X 0 2+(132269637/312500000 : ℝ)*X 1 0+(4737370707/10000000000 : ℝ)*X 1 1+(1886757723/5000000000 : ℝ)*X 1 2+(132269637/312500000 : ℝ)*X 2 0+(4737370707/10000000000 : ℝ)*X 2 1+(1886757723/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (733216348919777077256324427/83796875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69421893/50000000000000 : ℝ)*(base1) + (1824717621/100000000000000 : ℝ)*(base19) + (1803465553/100000000000000 : ℝ)*(base23) + (121418419/100000000000000 : ℝ)*(upper3) + (315286193/100000000000000 : ℝ)*(upper5) + (849207608083453/50000000000000 : ℝ)*(major0) + (849207608083453/50000000000000 : ℝ)*(major1) + (849207608083453/50000000000000 : ℝ)*(major2) + (1190581880827633/50000000000000 : ℝ)*(sp0) + (595294608086631/25000000000000 : ℝ)*(sp1) + (2381178453598593/100000000000000 : ℝ)*(sp2) + (40625742143083/4000000000000 : ℝ)*(sp3) + (3326850533/20000000000000 : ℝ)*(sp4) + (3095592319/50000000000000 : ℝ)*(sp7) + (1015649883605501/100000000000000 : ℝ)*(f.failure) + (1190590128532073/50000000000000 : ℝ)*(f.sum) + (10758318692643/13407500000000000000000000000 : ℝ)*base65 + (848911961118012691/335187500000000000000000000000000 : ℝ)*base67 + (3095361443224012691/335187500000000000000000000000000 : ℝ)*base69 + (1175404057830262691/335187500000000000000000000000000 : ℝ)*base71 + (35038919931311/26815000000000000000000000000 : ℝ)*base73 + (1941454417731950191/335187500000000000000000000000000 : ℝ)*base75 + (212781076644075191/335187500000000000000000000000000 : ℝ)*base77 + (650303871040612309/335187500000000000000000000000000 : ℝ)*base80 + (28875573645281/26815000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (31326739/5000000000000000000000 : ℝ)*base89 + (31326739/5000000000000000000000 : ℝ)*base91 + (31326739/5000000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (53551306491299574118646307/5237304687500000000000000000000 : ℝ) := by norm_num
    linear_combination (23001707/2000000000000 : ℝ)*(base19) + (2928879699/100000000000000 : ℝ)*(base23) + (150396399/100000000000000 : ℝ)*(upper3) + (180962109/100000000000000 : ℝ)*(lower4) + (22090677/5000000000000 : ℝ)*(upper5) + (216869154091397/12500000000000 : ℝ)*(major0) + (216869154091397/12500000000000 : ℝ)*(major1) + (216869154091397/12500000000000 : ℝ)*(major2) + (338711847/20000000000000 : ℝ)*(sp1) + (16669791201/100000000000000 : ℝ)*(sp2) + (152025409942943/6250000000000 : ℝ)*(sp4) + (304050464430313/12500000000000 : ℝ)*(sp5) + (608096740104047/25000000000000 : ℝ)*(sp6) + (1037499565542777/100000000000000 : ℝ)*(sp7) + (1037499565542777/100000000000000 : ℝ)*(f.failure) + (152025409942943/6250000000000 : ℝ)*(f.sum) + (26814381431449/6703750000000000000000000000 : ℝ)*base65 + (237623659961758933/41898437500000000000000000000000 : ℝ)*base68 + (575232832340783491/83796875000000000000000000000000 : ℝ)*base70 + (54591103825165183/41898437500000000000000000000000 : ℝ)*base72 + (41490861861191/26815000000000000000000000000 : ℝ)*base73 + (1007295908849720991/83796875000000000000000000000000 : ℝ)*base76 + (96112459657012279/20949218750000000000000000000000 : ℝ)*base78 + (596202586017783491/83796875000000000000000000000000 : ℝ)*base80 + (3841435771283/3351875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (35247703/5000000000000000000000 : ℝ)*base89 + (35247703/5000000000000000000000 : ℝ)*base91 + (35247703/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1560_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24877/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (137/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1791/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2231/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1560_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1560_s2_0 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-898373397/5000000000 : ℝ)*x 0 + (5444021653/10000000000 : ℝ)*x 1 + (1301120101/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898373397/5000000000 : ℝ)^4617 ≤ (11015816083163/100000000000000 : ℝ)^3593 := by
    have hnat : (898373397 : ℕ)^4617*100000000000000^3593 ≤ 11015816083163^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898373397 5000000000 11015816083163 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5444021653/10000000000 : ℝ)^4617 ≤ (9155611638737/20000000000000 : ℝ)^3593 := by
    have hnat : (5444021653 : ℕ)^4617*20000000000000^3593 ≤ 9155611638737^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5444021653 10000000000 9155611638737 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1301120101/2500000000 : ℝ)^4617 ≤ (21603062858961/50000000000000 : ℝ)^3593 := by
    have hnat : (1301120101 : ℕ)^4617*50000000000000^3593 ≤ 21603062858961^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1301120101 2500000000 21603062858961 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-898373397/5000000000 : ℝ), (5444021653/10000000000 : ℝ), (1301120101/2500000000 : ℝ)] ![(11015816083163/100000000000000 : ℝ), (9155611638737/20000000000000 : ℝ), (21603062858961/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-898373397/5000000000 : ℝ)|^4617 ≤ (11015816083163/100000000000000 : ℝ)^3593
        have hw : |(-898373397/5000000000 : ℝ)|=(898373397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5444021653/10000000000 : ℝ)|^4617 ≤ (9155611638737/20000000000000 : ℝ)^3593
        have hw : |(5444021653/10000000000 : ℝ)|=(5444021653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1301120101/2500000000 : ℝ)|^4617 ≤ (21603062858961/50000000000000 : ℝ)^3593
        have hw : |(1301120101/2500000000 : ℝ)|=(1301120101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s2_1 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676631307/5000000000 : ℝ)*x 0 + (-959874123/5000000000 : ℝ)*x 1 + (650560069/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676631307/5000000000 : ℝ)^4617 ≤ (2799981942191/6250000000000 : ℝ)^3593 := by
    have hnat : (2676631307 : ℕ)^4617*6250000000000^3593 ≤ 2799981942191^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676631307 5000000000 2799981942191 6250000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959874123/5000000000 : ℝ)^4617 ≤ (1199416161813/10000000000000 : ℝ)^3593 := by
    have hnat : (959874123 : ℕ)^4617*10000000000000^3593 ≤ 1199416161813^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959874123 5000000000 1199416161813 10000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (650560069/1250000000 : ℝ)^4617 ≤ (2160306364837/5000000000000 : ℝ)^3593 := by
    have hnat : (650560069 : ℕ)^4617*5000000000000^3593 ≤ 2160306364837^3593*1250000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650560069 1250000000 2160306364837 5000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676631307/5000000000 : ℝ), (-959874123/5000000000 : ℝ), (650560069/1250000000 : ℝ)] ![(2799981942191/6250000000000 : ℝ), (1199416161813/10000000000000 : ℝ), (2160306364837/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676631307/5000000000 : ℝ)|^4617 ≤ (2799981942191/6250000000000 : ℝ)^3593
        have hw : |(2676631307/5000000000 : ℝ)|=(2676631307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959874123/5000000000 : ℝ)|^4617 ≤ (1199416161813/10000000000000 : ℝ)^3593
        have hw : |(-959874123/5000000000 : ℝ)|=(959874123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(650560069/1250000000 : ℝ)|^4617 ≤ (2160306364837/5000000000000 : ℝ)^3593
        have hw : |(650560069/1250000000 : ℝ)|=(650560069/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s2_2 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353262561/10000000000 : ℝ)*x 0 + (2602240399/5000000000 : ℝ)*x 1 + (-1919747989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353262561/10000000000 : ℝ)^4617 ≤ (11199927626277/25000000000000 : ℝ)^3593 := by
    have hnat : (5353262561 : ℕ)^4617*25000000000000^3593 ≤ 11199927626277^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353262561 10000000000 11199927626277 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2602240399/5000000000 : ℝ)^4617 ≤ (21603064960497/50000000000000 : ℝ)^3593 := by
    have hnat : (2602240399 : ℕ)^4617*50000000000000^3593 ≤ 21603064960497^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602240399 5000000000 21603064960497 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919747989/10000000000 : ℝ)^4617 ≤ (2398831910967/20000000000000 : ℝ)^3593 := by
    have hnat : (1919747989 : ℕ)^4617*20000000000000^3593 ≤ 2398831910967^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919747989 10000000000 2398831910967 20000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353262561/10000000000 : ℝ), (2602240399/5000000000 : ℝ), (-1919747989/10000000000 : ℝ)] ![(11199927626277/25000000000000 : ℝ), (21603064960497/50000000000000 : ℝ), (2398831910967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353262561/10000000000 : ℝ)|^4617 ≤ (11199927626277/25000000000000 : ℝ)^3593
        have hw : |(5353262561/10000000000 : ℝ)|=(5353262561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2602240399/5000000000 : ℝ)|^4617 ≤ (21603064960497/50000000000000 : ℝ)^3593
        have hw : |(2602240399/5000000000 : ℝ)|=(2602240399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1919747989/10000000000 : ℝ)|^4617 ≤ (2398831910967/20000000000000 : ℝ)^3593
        have hw : |(-1919747989/10000000000 : ℝ)|=(1919747989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s2_3 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132694483/312500000 : ℝ)*x 0 + (1986499061/5000000000 : ℝ)*x 1 + (2267299017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132694483/312500000 : ℝ)^4617 ≤ (16632371540019/50000000000000 : ℝ)^3593 := by
    have hnat : (132694483 : ℕ)^4617*50000000000000^3593 ≤ 16632371540019^3593*312500000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132694483 312500000 16632371540019 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986499061/5000000000 : ℝ)^4617 ≤ (30539902777699/100000000000000 : ℝ)^3593 := by
    have hnat : (1986499061 : ℕ)^4617*100000000000000^3593 ≤ 30539902777699^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986499061 5000000000 30539902777699 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2267299017/5000000000 : ℝ)^4617 ≤ (9048838532219/25000000000000 : ℝ)^3593 := by
    have hnat : (2267299017 : ℕ)^4617*25000000000000^3593 ≤ 9048838532219^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267299017 5000000000 9048838532219 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132694483/312500000 : ℝ), (1986499061/5000000000 : ℝ), (2267299017/5000000000 : ℝ)] ![(16632371540019/50000000000000 : ℝ), (30539902777699/100000000000000 : ℝ), (9048838532219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132694483/312500000 : ℝ)|^4617 ≤ (16632371540019/50000000000000 : ℝ)^3593
        have hw : |(132694483/312500000 : ℝ)|=(132694483/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1986499061/5000000000 : ℝ)|^4617 ≤ (30539902777699/100000000000000 : ℝ)^3593
        have hw : |(1986499061/5000000000 : ℝ)|=(1986499061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2267299017/5000000000 : ℝ)|^4617 ≤ (9048838532219/25000000000000 : ℝ)^3593
        have hw : |(2267299017/5000000000 : ℝ)|=(2267299017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s2_4 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1796788323/10000000000 : ℝ)*x 0 + (5205917897/10000000000 : ℝ)*x 1 + (2721286043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1796788323/10000000000 : ℝ)^4617 ≤ (11016143262117/100000000000000 : ℝ)^3593 := by
    have hnat : (1796788323 : ℕ)^4617*100000000000000^3593 ≤ 11016143262117^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796788323 10000000000 11016143262117 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205917897/10000000000 : ℝ)^4617 ≤ (21610730529417/50000000000000 : ℝ)^3593 := by
    have hnat : (5205917897 : ℕ)^4617*50000000000000^3593 ≤ 21610730529417^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205917897 10000000000 21610730529417 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721286043/5000000000 : ℝ)^4617 ≤ (22881197830431/50000000000000 : ℝ)^3593 := by
    have hnat : (2721286043 : ℕ)^4617*50000000000000^3593 ≤ 22881197830431^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721286043 5000000000 22881197830431 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1796788323/10000000000 : ℝ), (5205917897/10000000000 : ℝ), (2721286043/5000000000 : ℝ)] ![(11016143262117/100000000000000 : ℝ), (21610730529417/50000000000000 : ℝ), (22881197830431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1796788323/10000000000 : ℝ)|^4617 ≤ (11016143262117/100000000000000 : ℝ)^3593
        have hw : |(-1796788323/10000000000 : ℝ)|=(1796788323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205917897/10000000000 : ℝ)|^4617 ≤ (21610730529417/50000000000000 : ℝ)^3593
        have hw : |(5205917897/10000000000 : ℝ)|=(5205917897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721286043/5000000000 : ℝ)|^4617 ≤ (22881197830431/50000000000000 : ℝ)^3593
        have hw : |(2721286043/5000000000 : ℝ)|=(2721286043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s2_5 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528995677/1000000000 : ℝ)*x 0 + (-336331459/2000000000 : ℝ)*x 1 + (2721286243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528995677/1000000000 : ℝ)^4617 ≤ (44120087273391/100000000000000 : ℝ)^3593 := by
    have hnat : (528995677 : ℕ)^4617*100000000000000^3593 ≤ 44120087273391^3593*1000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528995677 1000000000 44120087273391 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336331459/2000000000 : ℝ)^4617 ≤ (10117512725213/100000000000000 : ℝ)^3593 := by
    have hnat : (336331459 : ℕ)^4617*100000000000000^3593 ≤ 10117512725213^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336331459 2000000000 10117512725213 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721286243/5000000000 : ℝ)^4617 ≤ (1430074999459/3125000000000 : ℝ)^3593 := by
    have hnat : (2721286243 : ℕ)^4617*3125000000000^3593 ≤ 1430074999459^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721286243 5000000000 1430074999459 3125000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528995677/1000000000 : ℝ), (-336331459/2000000000 : ℝ), (2721286243/5000000000 : ℝ)] ![(44120087273391/100000000000000 : ℝ), (10117512725213/100000000000000 : ℝ), (1430074999459/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528995677/1000000000 : ℝ)|^4617 ≤ (44120087273391/100000000000000 : ℝ)^3593
        have hw : |(528995677/1000000000 : ℝ)|=(528995677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336331459/2000000000 : ℝ)|^4617 ≤ (10117512725213/100000000000000 : ℝ)^3593
        have hw : |(-336331459/2000000000 : ℝ)|=(336331459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721286243/5000000000 : ℝ)|^4617 ≤ (1430074999459/3125000000000 : ℝ)^3593
        have hw : |(2721286243/5000000000 : ℝ)|=(2721286243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s2_6 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289956823/10000000000 : ℝ)*x 0 + (2721286857/5000000000 : ℝ)*x 1 + (-336331101/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289956823/10000000000 : ℝ)^4617 ≤ (44120087841409/100000000000000 : ℝ)^3593 := by
    have hnat : (5289956823 : ℕ)^4617*100000000000000^3593 ≤ 44120087841409^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289956823 10000000000 44120087841409 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721286857/5000000000 : ℝ)^4617 ≤ (11440603312673/25000000000000 : ℝ)^3593 := by
    have hnat : (2721286857 : ℕ)^4617*25000000000000^3593 ≤ 11440603312673^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721286857 5000000000 11440603312673 25000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336331101/2000000000 : ℝ)^4617 ≤ (5058749443311/50000000000000 : ℝ)^3593 := by
    have hnat : (336331101 : ℕ)^4617*50000000000000^3593 ≤ 5058749443311^3593*2000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336331101 2000000000 5058749443311 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289956823/10000000000 : ℝ), (2721286857/5000000000 : ℝ), (-336331101/2000000000 : ℝ)] ![(44120087841409/100000000000000 : ℝ), (11440603312673/25000000000000 : ℝ), (5058749443311/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289956823/10000000000 : ℝ)|^4617 ≤ (44120087841409/100000000000000 : ℝ)^3593
        have hw : |(5289956823/10000000000 : ℝ)|=(5289956823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721286857/5000000000 : ℝ)|^4617 ≤ (11440603312673/25000000000000 : ℝ)^3593
        have hw : |(2721286857/5000000000 : ℝ)|=(2721286857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-336331101/2000000000 : ℝ)|^4617 ≤ (5058749443311/50000000000000 : ℝ)^3593
        have hw : |(-336331101/2000000000 : ℝ)|=(336331101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1560_s2_7 (p : ℝ) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061580347/2500000000 : ℝ)*x 0 + (4531229303/10000000000 : ℝ)*x 1 + (1988197811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061580347/2500000000 : ℝ)^4617 ≤ (16632864464107/50000000000000 : ℝ)^3593 := by
    have hnat : (1061580347 : ℕ)^4617*50000000000000^3593 ≤ 16632864464107^3593*2500000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061580347 2500000000 16632864464107 50000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4531229303/10000000000 : ℝ)^4617 ≤ (36160805004959/100000000000000 : ℝ)^3593 := by
    have hnat : (4531229303 : ℕ)^4617*100000000000000^3593 ≤ 36160805004959^3593*10000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531229303 10000000000 36160805004959 100000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1988197811/5000000000 : ℝ)^4617 ≤ (3057346605193/10000000000000 : ℝ)^3593 := by
    have hnat : (1988197811 : ℕ)^4617*10000000000000^3593 ≤ 3057346605193^3593*5000000000^4617 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1988197811 5000000000 3057346605193 10000000000000 4617 3593 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4617/1024 : ℝ)) 4617 3593 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061580347/2500000000 : ℝ), (4531229303/10000000000 : ℝ), (1988197811/5000000000 : ℝ)] ![(16632864464107/50000000000000 : ℝ), (36160805004959/100000000000000 : ℝ), (3057346605193/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061580347/2500000000 : ℝ)|^4617 ≤ (16632864464107/50000000000000 : ℝ)^3593
        have hw : |(1061580347/2500000000 : ℝ)|=(1061580347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4531229303/10000000000 : ℝ)|^4617 ≤ (36160805004959/100000000000000 : ℝ)^3593
        have hw : |(4531229303/10000000000 : ℝ)|=(4531229303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1988197811/5000000000 : ℝ)|^4617 ≤ (3057346605193/10000000000000 : ℝ)^3593
        have hw : |(1988197811/5000000000 : ℝ)|=(1988197811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1560_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2231/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1791/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5381/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15839/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2231/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1791/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2231/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1791/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2231/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1791/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2231/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1791/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2231/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1791/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2231/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1791/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1791/20000 : ℝ) ^ (4615/1024 : ℝ) ≤ (946458434889003/50000000000000000000 : ℝ) := by
    have hpowers : (1791/20000 : ℝ)^4615 ≤ (946458434889003/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1791 : ℕ)^4615*50000000000000000000^1024 ≤ 946458434889003^1024*20000^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1791 20000 946458434889003 50000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1791/20000 : ℝ)) (X := (946458434889003/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2231/12500 : ℝ) ^ (4615/1024 : ℝ) ≤ (2118394913960229/5000000000000000000 : ℝ) := by
    have hpowers : (2231/12500 : ℝ)^4615 ≤ (2118394913960229/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2231 : ℕ)^4615*5000000000000000000^1024 ≤ 2118394913960229^1024*12500^4615 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2231 12500 2118394913960229 5000000000000000000 4615 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2231/12500 : ℝ)) (X := (2118394913960229/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000946458434889003/25000000000000000000 : ℝ) ≤ (10000084000794161/10000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (25000946458434889003/25000000000000000000 : ℝ)^1024 ≤ (10000084000794161/10000000000000000 : ℝ)^4615 := by
      have hnat : (25000946458434889003 : ℕ)^1024*10000000000000000^4615 ≤ 10000084000794161^4615*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000946458434889003 25000000000000000000 10000084000794161 10000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084000794161/10000000000000000 : ℝ)) (X := (25000946458434889003/25000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022130407574491293/50000000000000000000 : ℝ) ≤ (2000196382544427/2000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (50022130407574491293/50000000000000000000 : ℝ)^1024 ≤ (2000196382544427/2000000000000000 : ℝ)^4615 := by
      have hnat : (50022130407574491293 : ℕ)^1024*2000000000000000^4615 ≤ 2000196382544427^4615*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022130407574491293 50000000000000000000 2000196382544427 2000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000196382544427/2000000000000000 : ℝ)) (X := (50022130407574491293/50000000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2502118394913960229/2500000000000000000 : ℝ) ≤ (10001879824650109/10000000000000000 : ℝ) ^ (4615/1024 : ℝ) := by
    have hpowers : (2502118394913960229/2500000000000000000 : ℝ)^1024 ≤ (10001879824650109/10000000000000000 : ℝ)^4615 := by
      have hnat : (2502118394913960229 : ℕ)^1024*10000000000000000^4615 ≤ 10001879824650109^4615*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2502118394913960229 2500000000000000000 10001879824650109 10000000000000000 1024 4615 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001879824650109/10000000000000000 : ℝ)) (X := (2502118394913960229/2500000000000000000 : ℝ)) (by norm_num) 4615 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(946458434889003/50000000000000000000 : ℝ) ≤ ((88914665416432459433/88930000000000000000 : ℝ)+2*(448955963987/444650000000000 : ℝ)*(1791/20000 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (88914665416432459433/88930000000000000000 : ℝ)+2*(448955963987/444650000000000 : ℝ)*(1791/20000 : ℝ)=(10000084000794161/10000000000000000 : ℝ) by norm_num, show 1+2*(946458434889003/50000000000000000000 : ℝ)=(25000946458434889003/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2118394913960229/5000000000000000000 : ℝ)+(946458434889003/50000000000000000000 : ℝ) ≤ ((88914665416432459433/88930000000000000000 : ℝ)+(448955963987/444650000000000 : ℝ)*((2231/12500 : ℝ)+(1791/20000 : ℝ)))^(4615/1024 : ℝ) := by
    rw [show (88914665416432459433/88930000000000000000 : ℝ)+(448955963987/444650000000000 : ℝ)*((2231/12500 : ℝ)+(1791/20000 : ℝ))=(2000196382544427/2000000000000000 : ℝ) by norm_num, show 1+(2118394913960229/5000000000000000000 : ℝ)+(946458434889003/50000000000000000000 : ℝ)=(50022130407574491293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2118394913960229/5000000000000000000 : ℝ) ≤ ((88914665416432459433/88930000000000000000 : ℝ)+2*(448955963987/444650000000000 : ℝ)*(2231/12500 : ℝ))^(4615/1024 : ℝ) := by
    rw [show (88914665416432459433/88930000000000000000 : ℝ)+2*(448955963987/444650000000000 : ℝ)*(2231/12500 : ℝ)=(10001879824650109/10000000000000000 : ℝ) by norm_num, show 1+2*(2118394913960229/5000000000000000000 : ℝ)=(2502118394913960229/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88914665416432459433/88930000000000000000 : ℝ)*(X 1 0+X 2 0)+(448955963987/444650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (1791/20000 : ℝ)) (hi := (2231/12500 : ℝ)) (c := (88914665416432459433/88930000000000000000 : ℝ)) (alpha := (448955963987/444650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88914665416432459433/88930000000000000000 : ℝ)*(X 0 1+X 2 1)+(448955963987/444650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (1791/20000 : ℝ)) (hi := (2231/12500 : ℝ)) (c := (88914665416432459433/88930000000000000000 : ℝ)) (alpha := (448955963987/444650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88914665416432459433/88930000000000000000 : ℝ)*(X 0 2+X 1 2)+(448955963987/444650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4615/1024 : ℝ)) (lo := (1791/20000 : ℝ)) (hi := (2231/12500 : ℝ)) (c := (88914665416432459433/88930000000000000000 : ℝ)) (alpha := (448955963987/444650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-898373397/5000000000 : ℝ)*X 0 0+(5444021653/10000000000 : ℝ)*X 0 1+(1301120101/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676631307/5000000000 : ℝ)*X 1 0+(-959874123/5000000000 : ℝ)*X 1 1+(650560069/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353262561/10000000000 : ℝ)*X 2 0+(2602240399/5000000000 : ℝ)*X 2 1+(-1919747989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((132694483/312500000 : ℝ)*X 0 0+(1986499061/5000000000 : ℝ)*X 0 1+(2267299017/5000000000 : ℝ)*X 0 2+(132694483/312500000 : ℝ)*X 1 0+(1986499061/5000000000 : ℝ)*X 1 1+(2267299017/5000000000 : ℝ)*X 1 2+(132694483/312500000 : ℝ)*X 2 0+(1986499061/5000000000 : ℝ)*X 2 1+(2267299017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1796788323/10000000000 : ℝ)*X 0 0+(5205917897/10000000000 : ℝ)*X 0 1+(2721286043/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((528995677/1000000000 : ℝ)*X 1 0+(-336331459/2000000000 : ℝ)*X 1 1+(2721286243/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289956823/10000000000 : ℝ)*X 2 0+(2721286857/5000000000 : ℝ)*X 2 1+(-336331101/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1061580347/2500000000 : ℝ)*X 0 0+(4531229303/10000000000 : ℝ)*X 0 1+(1988197811/5000000000 : ℝ)*X 0 2+(1061580347/2500000000 : ℝ)*X 1 0+(4531229303/10000000000 : ℝ)*X 1 1+(1988197811/5000000000 : ℝ)*X 1 2+(1061580347/2500000000 : ℝ)*X 2 0+(4531229303/10000000000 : ℝ)*X 2 1+(1988197811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1560_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1127460437926394346900066927/138953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1083025839/100000000000000 : ℝ)*(base19) + (47346447/6250000000000 : ℝ)*(base23) + (76056801/50000000000000 : ℝ)*(lower2) + (42306211/50000000000000 : ℝ)*(upper3) + (90745041/100000000000000 : ℝ)*(upper5) + (93051920376451/3125000000000 : ℝ)*(major0) + (93051920376451/3125000000000 : ℝ)*(major1) + (93051920376451/3125000000000 : ℝ)*(major2) + (33397315723587/800000000000 : ℝ)*(sp0) + (2087342118708423/50000000000000 : ℝ)*(sp1) + (1043671140724883/25000000000000 : ℝ)*(sp2) + (445157952237763/25000000000000 : ℝ)*(sp3) + (2085499431/10000000000000 : ℝ)*(sp4) + (2752116851/50000000000000 : ℝ)*(sp7) + (356127462636951/20000000000000 : ℝ)*(f.failure) + (834937064088537/20000000000000 : ℝ)*(f.sum) + (26953057353753/2779062500000000000000000000 : ℝ)*base65 + (526604592187943533/277906250000000000000000000000000 : ℝ)*base67 + (3136551529898537283/277906250000000000000000000000000 : ℝ)*base69 + (1814098244671037283/277906250000000000000000000000000 : ℝ)*base71 + (23289995796729/22232500000000000000000000000 : ℝ)*base73 + (1005509480805537283/277906250000000000000000000000000 : ℝ)*base75 + (3861037291885287283/277906250000000000000000000000000 : ℝ)*base77 + (413095537929650217/277906250000000000000000000000000 : ℝ)*base80 + (719400622959/86845703125000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2756711/1000000000000000000000 : ℝ)*base90 + (2756711/1000000000000000000000 : ℝ)*base92 + (2756711/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (457688698597148491331656683/44465000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2561157/100000000000000 : ℝ)*(base15) + (23562737/10000000000000 : ℝ)*(lower2) + (118937887/100000000000000 : ℝ)*(upper3) + (16576297/50000000000000 : ℝ)*(lower4) + (17318393/50000000000000 : ℝ)*(upper5) + (30139616369417/1000000000000 : ℝ)*(major0) + (30139616369417/1000000000000 : ℝ)*(major1) + (30139616369417/1000000000000 : ℝ)*(major2) + (2045063403/100000000000000 : ℝ)*(sp1) + (15340787363/50000000000000 : ℝ)*(sp2) + (105639453966333/2500000000000 : ℝ)*(sp4) + (105639402775719/2500000000000 : ℝ)*(sp5) + (2112773738539297/50000000000000 : ℝ)*(sp6) + (1802344772122237/100000000000000 : ℝ)*(sp7) + (1802344772122237/100000000000000 : ℝ)*(f.failure) + (105639453966333/2500000000000 : ℝ)*(f.sum) + (9138166855767/2223250000000000000000000000 : ℝ)*base66 + (963919320509269439/88930000000000000000000000000000 : ℝ)*base68 + (726026977619540561/88930000000000000000000000000000 : ℝ)*base69 + (908208832719979439/88930000000000000000000000000000 : ℝ)*base72 + (22085027028229/8893000000000000000000000000 : ℝ)*base74 + (169312285003739439/88930000000000000000000000000000 : ℝ)*base76 + (115290138411440561/88930000000000000000000000000000 : ℝ)*base77 + (1237745588745589439/88930000000000000000000000000000 : ℝ)*base80 + (7012920271917/889300000000000000000000000 : ℝ)*base81 + (17258643/5000000000000000000000 : ℝ)*base89 + (17258643/5000000000000000000000 : ℝ)*base91 + (17258643/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1560_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2231/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1791/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15839/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1560_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1560_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15839/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1560_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1560_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1560_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4615/1024 : ℝ) ≤ p) (hpb : p ≤ (4617/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83612239/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5381/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15839/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1560_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
