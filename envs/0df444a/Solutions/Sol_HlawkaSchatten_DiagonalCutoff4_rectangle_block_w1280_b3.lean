-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1280_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:22:59.972976+00:00
-- url     : https://prove2.me/submissions/7114e8b2-183b-4198-bc38-0a2bd9d3297c

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
theorem support_rectangle_w1280_box_0 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1926415871/10000000000 : ℝ)*x 0 + (5392503523/10000000000 : ℝ)*x 1 + (5392503063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926415871/10000000000 : ℝ)^265 ≤ (2280545623017/20000000000000 : ℝ)^201 := by
    have hnat : (1926415871 : ℕ)^265*20000000000000^201 ≤ 2280545623017^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926415871 10000000000 2280545623017 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392503523/10000000000 : ℝ)^265 ≤ (44298638422029/100000000000000 : ℝ)^201 := by
    have hnat : (5392503523 : ℕ)^265*100000000000000^201 ≤ 44298638422029^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392503523 10000000000 44298638422029 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392503063/10000000000 : ℝ)^265 ≤ (8859726687997/20000000000000 : ℝ)^201 := by
    have hnat : (5392503063 : ℕ)^265*20000000000000^201 ≤ 8859726687997^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392503063 10000000000 8859726687997 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1926415871/10000000000 : ℝ), (5392503523/10000000000 : ℝ), (5392503063/10000000000 : ℝ)] ![(2280545623017/20000000000000 : ℝ), (44298638422029/100000000000000 : ℝ), (8859726687997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1926415871/10000000000 : ℝ)|^265 ≤ (2280545623017/20000000000000 : ℝ)^201
        have hw : |(-1926415871/10000000000 : ℝ)|=(1926415871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392503523/10000000000 : ℝ)|^265 ≤ (44298638422029/100000000000000 : ℝ)^201
        have hw : |(5392503523/10000000000 : ℝ)|=(5392503523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392503063/10000000000 : ℝ)|^265 ≤ (8859726687997/20000000000000 : ℝ)^201
        have hw : |(5392503063/10000000000 : ℝ)|=(5392503063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_1 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (165129493/312500000 : ℝ)*x 0 + (-1037268071/5000000000 : ℝ)*x 1 + (1348125869/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165129493/312500000 : ℝ)^265 ≤ (5391102070747/12500000000000 : ℝ)^201 := by
    have hnat : (165129493 : ℕ)^265*12500000000000^201 ≤ 5391102070747^201*312500000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165129493 312500000 5391102070747 12500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037268071/5000000000 : ℝ)^265 ≤ (2514509100323/20000000000000 : ℝ)^201 := by
    have hnat : (1037268071 : ℕ)^265*20000000000000^201 ≤ 2514509100323^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037268071 5000000000 2514509100323 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348125869/2500000000 : ℝ)^265 ≤ (8859727582599/20000000000000 : ℝ)^201 := by
    have hnat : (1348125869 : ℕ)^265*20000000000000^201 ≤ 8859727582599^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348125869 2500000000 8859727582599 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165129493/312500000 : ℝ), (-1037268071/5000000000 : ℝ), (1348125869/2500000000 : ℝ)] ![(5391102070747/12500000000000 : ℝ), (2514509100323/20000000000000 : ℝ), (8859727582599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165129493/312500000 : ℝ)|^265 ≤ (5391102070747/12500000000000 : ℝ)^201
        have hw : |(165129493/312500000 : ℝ)|=(165129493/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1037268071/5000000000 : ℝ)|^265 ≤ (2514509100323/20000000000000 : ℝ)^201
        have hw : |(-1037268071/5000000000 : ℝ)|=(1037268071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348125869/2500000000 : ℝ)|^265 ≤ (8859727582599/20000000000000 : ℝ)^201
        have hw : |(1348125869/2500000000 : ℝ)|=(1348125869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_2 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (528414417/1000000000 : ℝ)*x 0 + (2696251777/5000000000 : ℝ)*x 1 + (-1037267753/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528414417/1000000000 : ℝ)^265 ≤ (21564410402857/50000000000000 : ℝ)^201 := by
    have hnat : (528414417 : ℕ)^265*50000000000000^201 ≤ 21564410402857^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528414417 1000000000 21564410402857 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696251777/5000000000 : ℝ)^265 ≤ (2768664922361/6250000000000 : ℝ)^201 := by
    have hnat : (2696251777 : ℕ)^265*6250000000000^201 ≤ 2768664922361^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696251777 5000000000 2768664922361 6250000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037267753/5000000000 : ℝ)^265 ≤ (6286270209957/50000000000000 : ℝ)^201 := by
    have hnat : (1037267753 : ℕ)^265*50000000000000^201 ≤ 6286270209957^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037267753 5000000000 6286270209957 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528414417/1000000000 : ℝ), (2696251777/5000000000 : ℝ), (-1037267753/5000000000 : ℝ)] ![(21564410402857/50000000000000 : ℝ), (2768664922361/6250000000000 : ℝ), (6286270209957/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528414417/1000000000 : ℝ)|^265 ≤ (21564410402857/50000000000000 : ℝ)^201
        have hw : |(528414417/1000000000 : ℝ)|=(528414417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696251777/5000000000 : ℝ)|^265 ≤ (2768664922361/6250000000000 : ℝ)^201
        have hw : |(2696251777/5000000000 : ℝ)|=(2696251777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1037267753/5000000000 : ℝ)|^265 ≤ (6286270209957/50000000000000 : ℝ)^201
        have hw : |(-1037267753/5000000000 : ℝ)|=(1037267753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_3 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (224641863/500000000 : ℝ)*x 0 + (4272264353/10000000000 : ℝ)*x 1 + (4272264271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224641863/500000000 : ℝ)^265 ≤ (34824148717273/100000000000000 : ℝ)^201 := by
    have hnat : (224641863 : ℕ)^265*100000000000000^201 ≤ 34824148717273^201*500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224641863 500000000 34824148717273 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4272264353/10000000000 : ℝ)^265 ≤ (32587926046691/100000000000000 : ℝ)^201 := by
    have hnat : (4272264353 : ℕ)^265*100000000000000^201 ≤ 32587926046691^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272264353 10000000000 32587926046691 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4272264271/10000000000 : ℝ)^265 ≤ (6517585044411/20000000000000 : ℝ)^201 := by
    have hnat : (4272264271 : ℕ)^265*20000000000000^201 ≤ 6517585044411^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4272264271 10000000000 6517585044411 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(224641863/500000000 : ℝ), (4272264353/10000000000 : ℝ), (4272264271/10000000000 : ℝ)] ![(34824148717273/100000000000000 : ℝ), (32587926046691/100000000000000 : ℝ), (6517585044411/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(224641863/500000000 : ℝ)|^265 ≤ (34824148717273/100000000000000 : ℝ)^201
        have hw : |(224641863/500000000 : ℝ)|=(224641863/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4272264353/10000000000 : ℝ)|^265 ≤ (32587926046691/100000000000000 : ℝ)^201
        have hw : |(4272264353/10000000000 : ℝ)|=(4272264353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4272264271/10000000000 : ℝ)|^265 ≤ (6517585044411/20000000000000 : ℝ)^201
        have hw : |(4272264271/10000000000 : ℝ)|=(4272264271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_4 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-90956119/400000000 : ℝ)*x 0 + (5263360693/10000000000 : ℝ)*x 1 + (657920131/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90956119/400000000 : ℝ)^265 ≤ (3547341508869/25000000000000 : ℝ)^201 := by
    have hnat : (90956119 : ℕ)^265*25000000000000^201 ≤ 3547341508869^201*400000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90956119 400000000 3547341508869 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263360693/10000000000 : ℝ)^265 ≤ (42905315069581/100000000000000 : ℝ)^201 := by
    have hnat : (5263360693 : ℕ)^265*100000000000000^201 ≤ 42905315069581^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263360693 10000000000 42905315069581 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657920131/1250000000 : ℝ)^265 ≤ (21452659442429/50000000000000 : ℝ)^201 := by
    have hnat : (657920131 : ℕ)^265*50000000000000^201 ≤ 21452659442429^201*1250000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657920131 1250000000 21452659442429 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90956119/400000000 : ℝ), (5263360693/10000000000 : ℝ), (657920131/1250000000 : ℝ)] ![(3547341508869/25000000000000 : ℝ), (42905315069581/100000000000000 : ℝ), (21452659442429/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90956119/400000000 : ℝ)|^265 ≤ (3547341508869/25000000000000 : ℝ)^201
        have hw : |(-90956119/400000000 : ℝ)|=(90956119/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263360693/10000000000 : ℝ)|^265 ≤ (42905315069581/100000000000000 : ℝ)^201
        have hw : |(5263360693/10000000000 : ℝ)|=(5263360693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657920131/1250000000 : ℝ)|^265 ≤ (21452659442429/50000000000000 : ℝ)^201
        have hw : |(657920131/1250000000 : ℝ)|=(657920131/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_5 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (268754633/500000000 : ℝ)*x 0 + (-2125894939/10000000000 : ℝ)*x 1 + (5263360949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268754633/500000000 : ℝ)^265 ≤ (44110166527733/100000000000000 : ℝ)^201 := by
    have hnat : (268754633 : ℕ)^265*100000000000000^201 ≤ 44110166527733^201*500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268754633 500000000 44110166527733 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125894939/10000000000 : ℝ)^265 ≤ (2596903126797/20000000000000 : ℝ)^201 := by
    have hnat : (2125894939 : ℕ)^265*20000000000000^201 ≤ 2596903126797^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125894939 10000000000 2596903126797 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263360949/10000000000 : ℝ)^265 ≤ (42905317820879/100000000000000 : ℝ)^201 := by
    have hnat : (5263360949 : ℕ)^265*100000000000000^201 ≤ 42905317820879^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263360949 10000000000 42905317820879 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268754633/500000000 : ℝ), (-2125894939/10000000000 : ℝ), (5263360949/10000000000 : ℝ)] ![(44110166527733/100000000000000 : ℝ), (2596903126797/20000000000000 : ℝ), (42905317820879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268754633/500000000 : ℝ)|^265 ≤ (44110166527733/100000000000000 : ℝ)^201
        have hw : |(268754633/500000000 : ℝ)|=(268754633/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2125894939/10000000000 : ℝ)|^265 ≤ (2596903126797/20000000000000 : ℝ)^201
        have hw : |(-2125894939/10000000000 : ℝ)|=(2125894939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263360949/10000000000 : ℝ)|^265 ≤ (42905317820879/100000000000000 : ℝ)^201
        have hw : |(5263360949/10000000000 : ℝ)|=(5263360949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_6 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (537509299/1000000000 : ℝ)*x 0 + (328960043/625000000 : ℝ)*x 1 + (-531473711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537509299/1000000000 : ℝ)^265 ≤ (4411017009813/10000000000000 : ℝ)^201 := by
    have hnat : (537509299 : ℕ)^265*10000000000000^201 ≤ 4411017009813^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537509299 1000000000 4411017009813 10000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (328960043/625000000 : ℝ)^265 ≤ (10726328753961/25000000000000 : ℝ)^201 := by
    have hnat : (328960043 : ℕ)^265*25000000000000^201 ≤ 10726328753961^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328960043 625000000 10726328753961 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531473711/2500000000 : ℝ)^265 ≤ (50720761207/390625000000 : ℝ)^201 := by
    have hnat : (531473711 : ℕ)^265*390625000000^201 ≤ 50720761207^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531473711 2500000000 50720761207 390625000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537509299/1000000000 : ℝ), (328960043/625000000 : ℝ), (-531473711/2500000000 : ℝ)] ![(4411017009813/10000000000000 : ℝ), (10726328753961/25000000000000 : ℝ), (50720761207/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537509299/1000000000 : ℝ)|^265 ≤ (4411017009813/10000000000000 : ℝ)^201
        have hw : |(537509299/1000000000 : ℝ)|=(537509299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(328960043/625000000 : ℝ)|^265 ≤ (10726328753961/25000000000000 : ℝ)^201
        have hw : |(328960043/625000000 : ℝ)|=(328960043/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-531473711/2500000000 : ℝ)|^265 ≤ (50720761207/390625000000 : ℝ)^201
        have hw : |(-531473711/2500000000 : ℝ)|=(531473711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_7 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1048132241/2500000000 : ℝ)*x 0 + (442236279/1000000000 : ℝ)*x 1 + (4422362497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048132241/2500000000 : ℝ)^265 ≤ (31788456978309/100000000000000 : ℝ)^201 := by
    have hnat : (1048132241 : ℕ)^265*100000000000000^201 ≤ 31788456978309^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048132241 2500000000 31788456978309 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442236279/1000000000 : ℝ)^265 ≤ (34105772990581/100000000000000 : ℝ)^201 := by
    have hnat : (442236279 : ℕ)^265*100000000000000^201 ≤ 34105772990581^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442236279 1000000000 34105772990581 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4422362497/10000000000 : ℝ)^265 ≤ (34105770011441/100000000000000 : ℝ)^201 := by
    have hnat : (4422362497 : ℕ)^265*100000000000000^201 ≤ 34105770011441^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4422362497 10000000000 34105770011441 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048132241/2500000000 : ℝ), (442236279/1000000000 : ℝ), (4422362497/10000000000 : ℝ)] ![(31788456978309/100000000000000 : ℝ), (34105772990581/100000000000000 : ℝ), (34105770011441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048132241/2500000000 : ℝ)|^265 ≤ (31788456978309/100000000000000 : ℝ)^201
        have hw : |(1048132241/2500000000 : ℝ)|=(1048132241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(442236279/1000000000 : ℝ)|^265 ≤ (34105772990581/100000000000000 : ℝ)^201
        have hw : |(442236279/1000000000 : ℝ)|=(442236279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4422362497/10000000000 : ℝ)|^265 ≤ (34105770011441/100000000000000 : ℝ)^201
        have hw : |(4422362497/10000000000 : ℝ)|=(4422362497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_8 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-2201109277/10000000000 : ℝ)*x 0 + (2587379667/5000000000 : ℝ)*x 1 + (5406544921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2201109277/10000000000 : ℝ)^265 ≤ (1359356782013/10000000000000 : ℝ)^201 := by
    have hnat : (2201109277 : ℕ)^265*10000000000000^201 ≤ 1359356782013^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201109277 10000000000 1359356782013 10000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2587379667/5000000000 : ℝ)^265 ≤ (1678226197571/4000000000000 : ℝ)^201 := by
    have hnat : (2587379667 : ℕ)^265*4000000000000^201 ≤ 1678226197571^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587379667 5000000000 1678226197571 4000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406544921/10000000000 : ℝ)^265 ≤ (2222538861307/5000000000000 : ℝ)^201 := by
    have hnat : (5406544921 : ℕ)^265*5000000000000^201 ≤ 2222538861307^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406544921 10000000000 2222538861307 5000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2201109277/10000000000 : ℝ), (2587379667/5000000000 : ℝ), (5406544921/10000000000 : ℝ)] ![(1359356782013/10000000000000 : ℝ), (1678226197571/4000000000000 : ℝ), (2222538861307/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2201109277/10000000000 : ℝ)|^265 ≤ (1359356782013/10000000000000 : ℝ)^201
        have hw : |(-2201109277/10000000000 : ℝ)|=(2201109277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2587379667/5000000000 : ℝ)|^265 ≤ (1678226197571/4000000000000 : ℝ)^201
        have hw : |(2587379667/5000000000 : ℝ)|=(2587379667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406544921/10000000000 : ℝ)|^265 ≤ (2222538861307/5000000000000 : ℝ)^201
        have hw : |(5406544921/10000000000 : ℝ)|=(5406544921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_9 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5274249461/10000000000 : ℝ)*x 0 + (-2068815007/10000000000 : ℝ)*x 1 + (337909009/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274249461/10000000000 : ℝ)^265 ≤ (21511189010839/50000000000000 : ℝ)^201 := by
    have hnat : (5274249461 : ℕ)^265*50000000000000^201 ≤ 21511189010839^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274249461 10000000000 21511189010839 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2068815007/10000000000 : ℝ)^265 ≤ (501074126531/4000000000000 : ℝ)^201 := by
    have hnat : (2068815007 : ℕ)^265*4000000000000^201 ≤ 501074126531^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2068815007 10000000000 501074126531 4000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337909009/625000000 : ℝ)^265 ≤ (44450768803847/100000000000000 : ℝ)^201 := by
    have hnat : (337909009 : ℕ)^265*100000000000000^201 ≤ 44450768803847^201*625000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337909009 625000000 44450768803847 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274249461/10000000000 : ℝ), (-2068815007/10000000000 : ℝ), (337909009/625000000 : ℝ)] ![(21511189010839/50000000000000 : ℝ), (501074126531/4000000000000 : ℝ), (44450768803847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274249461/10000000000 : ℝ)|^265 ≤ (21511189010839/50000000000000 : ℝ)^201
        have hw : |(5274249461/10000000000 : ℝ)|=(5274249461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2068815007/10000000000 : ℝ)|^265 ≤ (501074126531/4000000000000 : ℝ)^201
        have hw : |(-2068815007/10000000000 : ℝ)|=(2068815007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337909009/625000000 : ℝ)|^265 ≤ (44450768803847/100000000000000 : ℝ)^201
        have hw : |(337909009/625000000 : ℝ)|=(337909009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_10 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5274249699/10000000000 : ℝ)*x 0 + (2703272097/5000000000 : ℝ)*x 1 + (-1034407309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274249699/10000000000 : ℝ)^265 ≤ (4302238058121/10000000000000 : ℝ)^201 := by
    have hnat : (5274249699 : ℕ)^265*10000000000000^201 ≤ 4302238058121^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274249699 10000000000 4302238058121 10000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703272097/5000000000 : ℝ)^265 ≤ (22225384672911/50000000000000 : ℝ)^201 := by
    have hnat : (2703272097 : ℕ)^265*50000000000000^201 ≤ 22225384672911^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703272097 5000000000 22225384672911 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034407309/5000000000 : ℝ)^265 ≤ (12526850057859/100000000000000 : ℝ)^201 := by
    have hnat : (1034407309 : ℕ)^265*100000000000000^201 ≤ 12526850057859^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034407309 5000000000 12526850057859 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274249699/10000000000 : ℝ), (2703272097/5000000000 : ℝ), (-1034407309/5000000000 : ℝ)] ![(4302238058121/10000000000000 : ℝ), (22225384672911/50000000000000 : ℝ), (12526850057859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274249699/10000000000 : ℝ)|^265 ≤ (4302238058121/10000000000000 : ℝ)^201
        have hw : |(5274249699/10000000000 : ℝ)|=(5274249699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703272097/5000000000 : ℝ)|^265 ≤ (22225384672911/50000000000000 : ℝ)^201
        have hw : |(2703272097/5000000000 : ℝ)|=(2703272097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1034407309/5000000000 : ℝ)|^265 ≤ (12526850057859/100000000000000 : ℝ)^201
        have hw : |(-1034407309/5000000000 : ℝ)|=(1034407309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_11 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2262464533/5000000000 : ℝ)*x 0 + (2127965651/5000000000 : ℝ)*x 1 + (2127965027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2262464533/5000000000 : ℝ)^265 ≤ (17576234073911/50000000000000 : ℝ)^201 := by
    have hnat : (2262464533 : ℕ)^265*50000000000000^201 ≤ 17576234073911^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262464533 5000000000 17576234073911 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2127965651/5000000000 : ℝ)^265 ≤ (32423772187197/100000000000000 : ℝ)^201 := by
    have hnat : (2127965651 : ℕ)^265*100000000000000^201 ≤ 32423772187197^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127965651 5000000000 32423772187197 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127965027/5000000000 : ℝ)^265 ≤ (16211879825969/50000000000000 : ℝ)^201 := by
    have hnat : (2127965027 : ℕ)^265*50000000000000^201 ≤ 16211879825969^201*5000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127965027 5000000000 16211879825969 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2262464533/5000000000 : ℝ), (2127965651/5000000000 : ℝ), (2127965027/5000000000 : ℝ)] ![(17576234073911/50000000000000 : ℝ), (32423772187197/100000000000000 : ℝ), (16211879825969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2262464533/5000000000 : ℝ)|^265 ≤ (17576234073911/50000000000000 : ℝ)^201
        have hw : |(2262464533/5000000000 : ℝ)|=(2262464533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2127965651/5000000000 : ℝ)|^265 ≤ (32423772187197/100000000000000 : ℝ)^201
        have hw : |(2127965651/5000000000 : ℝ)|=(2127965651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2127965027/5000000000 : ℝ)|^265 ≤ (16211879825969/50000000000000 : ℝ)^201
        have hw : |(2127965027/5000000000 : ℝ)|=(2127965027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_12 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1999674313/10000000000 : ℝ)*x 0 + (5478751061/10000000000 : ℝ)*x 1 + (5252350743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1999674313/10000000000 : ℝ)^265 ≤ (5988928643271/50000000000000 : ℝ)^201 := by
    have hnat : (1999674313 : ℕ)^265*50000000000000^201 ≤ 5988928643271^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999674313 10000000000 5988928643271 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5478751061/10000000000 : ℝ)^265 ≤ (1130877875123/2500000000000 : ℝ)^201 := by
    have hnat : (5478751061 : ℕ)^265*2500000000000^201 ≤ 1130877875123^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5478751061 10000000000 1130877875123 2500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252350743/10000000000 : ℝ)^265 ≤ (21393513846181/50000000000000 : ℝ)^201 := by
    have hnat : (5252350743 : ℕ)^265*50000000000000^201 ≤ 21393513846181^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252350743 10000000000 21393513846181 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1999674313/10000000000 : ℝ), (5478751061/10000000000 : ℝ), (5252350743/10000000000 : ℝ)] ![(5988928643271/50000000000000 : ℝ), (1130877875123/2500000000000 : ℝ), (21393513846181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1999674313/10000000000 : ℝ)|^265 ≤ (5988928643271/50000000000000 : ℝ)^201
        have hw : |(-1999674313/10000000000 : ℝ)|=(1999674313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5478751061/10000000000 : ℝ)|^265 ≤ (1130877875123/2500000000000 : ℝ)^201
        have hw : |(5478751061/10000000000 : ℝ)|=(5478751061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252350743/10000000000 : ℝ)|^265 ≤ (21393513846181/50000000000000 : ℝ)^201
        have hw : |(5252350743/10000000000 : ℝ)|=(5252350743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_13 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5382843797/10000000000 : ℝ)*x 0 + (-2130166849/10000000000 : ℝ)*x 1 + (1050470103/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382843797/10000000000 : ℝ)^265 ≤ (5524256038343/12500000000000 : ℝ)^201 := by
    have hnat : (5382843797 : ℕ)^265*12500000000000^201 ≤ 5524256038343^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382843797 10000000000 5524256038343 12500000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2130166849/10000000000 : ℝ)^265 ≤ (3254731607481/25000000000000 : ℝ)^201 := by
    have hnat : (2130166849 : ℕ)^265*25000000000000^201 ≤ 3254731607481^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2130166849 10000000000 3254731607481 25000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1050470103/2000000000 : ℝ)^265 ≤ (2139351262181/5000000000000 : ℝ)^201 := by
    have hnat : (1050470103 : ℕ)^265*5000000000000^201 ≤ 2139351262181^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050470103 2000000000 2139351262181 5000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382843797/10000000000 : ℝ), (-2130166849/10000000000 : ℝ), (1050470103/2000000000 : ℝ)] ![(5524256038343/12500000000000 : ℝ), (3254731607481/25000000000000 : ℝ), (2139351262181/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382843797/10000000000 : ℝ)|^265 ≤ (5524256038343/12500000000000 : ℝ)^201
        have hw : |(5382843797/10000000000 : ℝ)|=(5382843797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2130166849/10000000000 : ℝ)|^265 ≤ (3254731607481/25000000000000 : ℝ)^201
        have hw : |(-2130166849/10000000000 : ℝ)|=(2130166849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1050470103/2000000000 : ℝ)|^265 ≤ (2139351262181/5000000000000 : ℝ)^201
        have hw : |(1050470103/2000000000 : ℝ)|=(1050470103/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_14 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5382843701/10000000000 : ℝ)*x 0 + (525235081/1000000000 : ℝ)*x 1 + (-426033317/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382843701/10000000000 : ℝ)^265 ≤ (22097023633803/50000000000000 : ℝ)^201 := by
    have hnat : (5382843701 : ℕ)^265*50000000000000^201 ≤ 22097023633803^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382843701 10000000000 22097023633803 50000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525235081/1000000000 : ℝ)^265 ≤ (42787028411949/100000000000000 : ℝ)^201 := by
    have hnat : (525235081 : ℕ)^265*100000000000000^201 ≤ 42787028411949^201*1000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525235081 1000000000 42787028411949 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426033317/2000000000 : ℝ)^265 ≤ (1301892430269/10000000000000 : ℝ)^201 := by
    have hnat : (426033317 : ℕ)^265*10000000000000^201 ≤ 1301892430269^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426033317 2000000000 1301892430269 10000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382843701/10000000000 : ℝ), (525235081/1000000000 : ℝ), (-426033317/2000000000 : ℝ)] ![(22097023633803/50000000000000 : ℝ), (42787028411949/100000000000000 : ℝ), (1301892430269/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382843701/10000000000 : ℝ)|^265 ≤ (22097023633803/50000000000000 : ℝ)^201
        have hw : |(5382843701/10000000000 : ℝ)|=(5382843701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525235081/1000000000 : ℝ)|^265 ≤ (42787028411949/100000000000000 : ℝ)^201
        have hw : |(525235081/1000000000 : ℝ)|=(525235081/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426033317/2000000000 : ℝ)|^265 ≤ (1301892430269/10000000000000 : ℝ)^201
        have hw : |(-426033317/2000000000 : ℝ)|=(426033317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1280_box_15 (p : ℝ) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1041619899/2500000000 : ℝ)*x 0 + (4435149699/10000000000 : ℝ)*x 1 + (887029779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041619899/2500000000 : ℝ)^265 ≤ (6305663056469/20000000000000 : ℝ)^201 := by
    have hnat : (1041619899 : ℕ)^265*20000000000000^201 ≤ 6305663056469^201*2500000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041619899 2500000000 6305663056469 20000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4435149699/10000000000 : ℝ)^265 ≤ (1711792322047/5000000000000 : ℝ)^201 := by
    have hnat : (4435149699 : ℕ)^265*5000000000000^201 ≤ 1711792322047^201*10000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4435149699 10000000000 1711792322047 5000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (887029779/2000000000 : ℝ)^265 ≤ (34235838258579/100000000000000 : ℝ)^201 := by
    have hnat : (887029779 : ℕ)^265*100000000000000^201 ≤ 34235838258579^201*2000000000^265 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887029779 2000000000 34235838258579 100000000000000 265 201 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (265/64 : ℝ)) 265 201 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041619899/2500000000 : ℝ), (4435149699/10000000000 : ℝ), (887029779/2000000000 : ℝ)] ![(6305663056469/20000000000000 : ℝ), (1711792322047/5000000000000 : ℝ), (34235838258579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041619899/2500000000 : ℝ)|^265 ≤ (6305663056469/20000000000000 : ℝ)^201
        have hw : |(1041619899/2500000000 : ℝ)|=(1041619899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4435149699/10000000000 : ℝ)|^265 ≤ (1711792322047/5000000000000 : ℝ)^201
        have hw : |(4435149699/10000000000 : ℝ)|=(4435149699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(887029779/2000000000 : ℝ)|^265 ≤ (34235838258579/100000000000000 : ℝ)^201
        have hw : |(887029779/2000000000 : ℝ)|=(887029779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1280_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15709/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29411/50000 : ℝ) ∧ (79583/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84107/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10997/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14663/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10997/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14663/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10997/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10997/100000 : ℝ) ^ (4239/1024 : ℝ) ≤ (214902931330499/2000000000000000000 : ℝ) := by
    have hpowers : (10997/100000 : ℝ)^4239 ≤ (214902931330499/2000000000000000000 : ℝ)^1024 := by
      have hnat : (10997 : ℕ)^4239*2000000000000000000^1024 ≤ 214902931330499^1024*100000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10997 100000 214902931330499 2000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10997/100000 : ℝ)) (X := (214902931330499/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14663/100000 : ℝ) ^ (4239/1024 : ℝ) ≤ (35355392252539287/100000000000000000000 : ℝ) := by
    have hpowers : (14663/100000 : ℝ)^4239 ≤ (35355392252539287/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14663 : ℕ)^4239*100000000000000000000^1024 ≤ 35355392252539287^1024*100000^4239 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14663 100000 35355392252539287 100000000000000000000 4239 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14663/100000 : ℝ)) (X := (35355392252539287/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000214902931330499/1000000000000000000 : ℝ) ≤ (5000259545494393/5000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (1000214902931330499/1000000000000000000 : ℝ)^1024 ≤ (5000259545494393/5000000000000000 : ℝ)^4239 := by
      have hnat : (1000214902931330499 : ℕ)^1024*5000000000000000^4239 ≤ 5000259545494393^4239*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000214902931330499 1000000000000000000 5000259545494393 5000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000259545494393/5000000000000000 : ℝ)) (X := (1000214902931330499/1000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046100538819064237/100000000000000000000 : ℝ) ≤ (10001113439519089/10000000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (100046100538819064237/100000000000000000000 : ℝ)^1024 ≤ (10001113439519089/10000000000000000 : ℝ)^4239 := by
      have hnat : (100046100538819064237 : ℕ)^1024*10000000000000000^4239 ≤ 10001113439519089^4239*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046100538819064237 100000000000000000000 10001113439519089 10000000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001113439519089/10000000000000000 : ℝ)) (X := (100046100538819064237/100000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035355392252539287/50000000000000000000 : ℝ) ≤ (625106736753087/625000000000000 : ℝ) ^ (4239/1024 : ℝ) := by
    have hpowers : (50035355392252539287/50000000000000000000 : ℝ)^1024 ≤ (625106736753087/625000000000000 : ℝ)^4239 := by
      have hnat : (50035355392252539287 : ℕ)^1024*625000000000000^4239 ≤ 625106736753087^4239*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035355392252539287 50000000000000000000 625106736753087 625000000000000 1024 4239 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625106736753087/625000000000000 : ℝ)) (X := (50035355392252539287/50000000000000000000 : ℝ)) (by norm_num) 4239 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(214902931330499/2000000000000000000 : ℝ) ≤ ((18324415442994702647/18330000000000000000 : ℝ)+2*(594348530303/366600000000000 : ℝ)*(10997/100000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (18324415442994702647/18330000000000000000 : ℝ)+2*(594348530303/366600000000000 : ℝ)*(10997/100000 : ℝ)=(5000259545494393/5000000000000000 : ℝ) by norm_num, show 1+2*(214902931330499/2000000000000000000 : ℝ)=(1000214902931330499/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35355392252539287/100000000000000000000 : ℝ)+(214902931330499/2000000000000000000 : ℝ) ≤ ((18324415442994702647/18330000000000000000 : ℝ)+(594348530303/366600000000000 : ℝ)*((14663/100000 : ℝ)+(10997/100000 : ℝ)))^(4239/1024 : ℝ) := by
    rw [show (18324415442994702647/18330000000000000000 : ℝ)+(594348530303/366600000000000 : ℝ)*((14663/100000 : ℝ)+(10997/100000 : ℝ))=(10001113439519089/10000000000000000 : ℝ) by norm_num, show 1+(35355392252539287/100000000000000000000 : ℝ)+(214902931330499/2000000000000000000 : ℝ)=(100046100538819064237/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35355392252539287/100000000000000000000 : ℝ) ≤ ((18324415442994702647/18330000000000000000 : ℝ)+2*(594348530303/366600000000000 : ℝ)*(14663/100000 : ℝ))^(4239/1024 : ℝ) := by
    rw [show (18324415442994702647/18330000000000000000 : ℝ)+2*(594348530303/366600000000000 : ℝ)*(14663/100000 : ℝ)=(625106736753087/625000000000000 : ℝ) by norm_num, show 1+2*(35355392252539287/100000000000000000000 : ℝ)=(50035355392252539287/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18324415442994702647/18330000000000000000 : ℝ)*(X 1 0+X 2 0)+(594348530303/366600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (18324415442994702647/18330000000000000000 : ℝ)) (alpha := (594348530303/366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18324415442994702647/18330000000000000000 : ℝ)*(X 0 1+X 2 1)+(594348530303/366600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (18324415442994702647/18330000000000000000 : ℝ)) (alpha := (594348530303/366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18324415442994702647/18330000000000000000 : ℝ)*(X 0 2+X 1 2)+(594348530303/366600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4239/1024 : ℝ)) (lo := (10997/100000 : ℝ)) (hi := (14663/100000 : ℝ)) (c := (18324415442994702647/18330000000000000000 : ℝ)) (alpha := (594348530303/366600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1926415871/10000000000 : ℝ)*X 0 0+(5392503523/10000000000 : ℝ)*X 0 1+(5392503063/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((165129493/312500000 : ℝ)*X 1 0+(-1037268071/5000000000 : ℝ)*X 1 1+(1348125869/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((528414417/1000000000 : ℝ)*X 2 0+(2696251777/5000000000 : ℝ)*X 2 1+(-1037267753/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((224641863/500000000 : ℝ)*X 0 0+(4272264353/10000000000 : ℝ)*X 0 1+(4272264271/10000000000 : ℝ)*X 0 2+(224641863/500000000 : ℝ)*X 1 0+(4272264353/10000000000 : ℝ)*X 1 1+(4272264271/10000000000 : ℝ)*X 1 2+(224641863/500000000 : ℝ)*X 2 0+(4272264353/10000000000 : ℝ)*X 2 1+(4272264271/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-90956119/400000000 : ℝ)*X 0 0+(5263360693/10000000000 : ℝ)*X 0 1+(657920131/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268754633/500000000 : ℝ)*X 1 0+(-2125894939/10000000000 : ℝ)*X 1 1+(5263360949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((537509299/1000000000 : ℝ)*X 2 0+(328960043/625000000 : ℝ)*X 2 1+(-531473711/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1048132241/2500000000 : ℝ)*X 0 0+(442236279/1000000000 : ℝ)*X 0 1+(4422362497/10000000000 : ℝ)*X 0 2+(1048132241/2500000000 : ℝ)*X 1 0+(442236279/1000000000 : ℝ)*X 1 1+(4422362497/10000000000 : ℝ)*X 1 2+(1048132241/2500000000 : ℝ)*X 2 0+(442236279/1000000000 : ℝ)*X 2 1+(4422362497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2201109277/10000000000 : ℝ)*X 0 0+(2587379667/5000000000 : ℝ)*X 0 1+(5406544921/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274249461/10000000000 : ℝ)*X 1 0+(-2068815007/10000000000 : ℝ)*X 1 1+(337909009/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274249699/10000000000 : ℝ)*X 2 0+(2703272097/5000000000 : ℝ)*X 2 1+(-1034407309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2262464533/5000000000 : ℝ)*X 0 0+(2127965651/5000000000 : ℝ)*X 0 1+(2127965027/5000000000 : ℝ)*X 0 2+(2262464533/5000000000 : ℝ)*X 1 0+(2127965651/5000000000 : ℝ)*X 1 1+(2127965027/5000000000 : ℝ)*X 1 2+(2262464533/5000000000 : ℝ)*X 2 0+(2127965651/5000000000 : ℝ)*X 2 1+(2127965027/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1999674313/10000000000 : ℝ)*X 0 0+(5478751061/10000000000 : ℝ)*X 0 1+(5252350743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5382843797/10000000000 : ℝ)*X 1 0+(-2130166849/10000000000 : ℝ)*X 1 1+(1050470103/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5382843701/10000000000 : ℝ)*X 2 0+(525235081/1000000000 : ℝ)*X 2 1+(-426033317/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1041619899/2500000000 : ℝ)*X 0 0+(4435149699/10000000000 : ℝ)*X 0 1+(887029779/2000000000 : ℝ)*X 0 2+(1041619899/2500000000 : ℝ)*X 1 0+(4435149699/10000000000 : ℝ)*X 1 1+(887029779/2000000000 : ℝ)*X 1 2+(1041619899/2500000000 : ℝ)*X 2 0+(4435149699/10000000000 : ℝ)*X 2 1+(887029779/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1280_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15709/25000 : ℝ) ≤ (-23994727680750501407524907688669/38187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32012183/100000000000000 : ℝ)*(upper1) + (41323673/50000000000000 : ℝ)*(lower2) + (4721451/100000000000000 : ℝ)*(lower3) + (852523/2500000000000 : ℝ)*(upper5) + (356294450857627/12500000000000 : ℝ)*(major0) + (356294450857627/12500000000000 : ℝ)*(major1) + (356294450857627/12500000000000 : ℝ)*(major2) + (4882171113/100000000000000 : ℝ)*(sp2) + (578653017/20000000000000 : ℝ)*(sp3) + (1925001142319107/50000000000000 : ℝ)*(sp4) + (1925001769641393/50000000000000 : ℝ)*(sp5) + (1924999328555837/50000000000000 : ℝ)*(sp6) + (116978090158941/6250000000000 : ℝ)*(sp7) + (313661143/25000000000000 : ℝ)*(sp12) + (935826167904071/50000000000000 : ℝ)*(f.failure) + (1925001769641393/50000000000000 : ℝ)*(f.sum) + (16474977919373/4582500000000000000000000000 : ℝ)*base66 + (305444484070071223/76375000000000000000000000000000 : ℝ)*base67 + (152767827288071223/76375000000000000000000000000000 : ℝ)*base69 + (750498609763196223/76375000000000000000000000000000 : ℝ)*base71 + (23322176431591/9165000000000000000000000000 : ℝ)*base74 + (535777134300178777/76375000000000000000000000000000 : ℝ)*base76 + (133387410088053777/76375000000000000000000000000000 : ℝ)*base78 + (203873820655071223/76375000000000000000000000000000 : ℝ)*base79 + (83440183115521/9165000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (81227699/5000000000000000000000 : ℝ)*base89 + (81227699/5000000000000000000000 : ℝ)*base91 + (81227699/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (29411/50000 : ℝ) ≤ (89854905429339122967606889490271/152750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2582943/3125000000000 : ℝ)*(upper0) + (28581439/50000000000000 : ℝ)*(lower1) + (317333001/100000000000000 : ℝ)*(upper4) + (2916988945233071/100000000000000 : ℝ)*(major0) + (2916988945233071/100000000000000 : ℝ)*(major1) + (182311809077067/6250000000000 : ℝ)*(major2) + (974738216371029/25000000000000 : ℝ)*(sp0) + (3898956379118723/100000000000000 : ℝ)*(sp1) + (1949469189228641/50000000000000 : ℝ)*(sp2) + (957700856349087/50000000000000 : ℝ)*(sp3) + (3454654271/50000000000000 : ℝ)*(sp5) + (24909969983/100000000000000 : ℝ)*(sp6) + (4617561239/100000000000000 : ℝ)*(sp7) + (10422943149/100000000000000 : ℝ)*(sp8) + (957703165129707/50000000000000 : ℝ)*(f.failure) + (779792657685453/20000000000000 : ℝ)*(f.sum) + (160596042983509/36660000000000000000000000000 : ℝ)*base65 + (18725016201018438937/1833000000000000000000000000000000 : ℝ)*base67 + (859982688701062237/57281250000000000000000000000000 : ℝ)*base69 + (27913336107264438937/1833000000000000000000000000000000 : ℝ)*base71 + (785115958888849/36660000000000000000000000000 : ℝ)*base73 + (542440415101780987/57281250000000000000000000000000 : ℝ)*base75 + (8852758856287762979/611000000000000000000000000000000 : ℝ)*base77 + (528224783289762979/611000000000000000000000000000000 : ℝ)*base79 + (64985443379177/18330000000000000000000000000 : ℝ)*base82 + (26745383/5000000000000000000000 : ℝ)*base89 + (26745383/5000000000000000000000 : ℝ)*base91 + (23254617/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79583/100000 : ℝ) ≤ (121567448834960180125580869497829/152750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (164182679/100000000000000 : ℝ)*(upper1) + (13207409/100000000000000 : ℝ)*(lower3) + (1318361/625000000000 : ℝ)*(upper4) + (4290407/50000000000000 : ℝ)*(lower5) + (646271867553079/20000000000000 : ℝ)*(major0) + (646271867553079/20000000000000 : ℝ)*(major1) + (807839834441349/25000000000000 : ℝ)*(major2) + (109410684351/100000000000000 : ℝ)*(sp2) + (111194818427/100000000000000 : ℝ)*(sp3) + (11023265283/100000000000000 : ℝ)*(sp4) + (67411641988163/1562500000000 : ℝ)*(sp8) + (1078589027626929/25000000000000 : ℝ)*(sp9) + (1078561674955841/25000000000000 : ℝ)*(sp10) + (66303835618711/3125000000000 : ℝ)*(sp11) + (106091696730859/5000000000000 : ℝ)*(f.failure) + (1078589027626929/25000000000000 : ℝ)*(f.sum) + (265886343130093/36660000000000000000000000000 : ℝ)*base65 + (4414695374926980113/366600000000000000000000000000000 : ℝ)*base67 + (3072501696531863303/458250000000000000000000000000000 : ℝ)*base69 + (321127050559380113/366600000000000000000000000000000 : ℝ)*base71 + (356710878708493/36660000000000000000000000000 : ℝ)*base73 + (1299793352085863303/458250000000000000000000000000000 : ℝ)*base75 + (1030395022752783371/122200000000000000000000000000000 : ℝ)*base77 + (1538889612189383371/122200000000000000000000000000000 : ℝ)*base79 + (6655326969823/733200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (1226471/500000000000000000000 : ℝ)*base89 + (1226471/500000000000000000000 : ℝ)*base91 + (3773529/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-84107/100000 : ℝ) ≤ (-9882266546490330957035650934543/11750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15770653/12500000000000 : ℝ)*(lower0) + (44297029/50000000000000 : ℝ)*(lower2) + (476059/25000000000000 : ℝ)*(upper3) + (3267120928044003/100000000000000 : ℝ)*(major0) + (3267120928044003/100000000000000 : ℝ)*(major1) + (816780232011001/25000000000000 : ℝ)*(major2) + (13320018427/100000000000000 : ℝ)*(sp0) + (26274539099/10000000000000 : ℝ)*(sp5) + (46873554361/50000000000000 : ℝ)*(sp6) + (11511115781/25000000000000 : ℝ)*(sp7) + (4416946974388489/100000000000000 : ℝ)*(sp12) + (2208348774507963/50000000000000 : ℝ)*(sp13) + (2208433273649097/50000000000000 : ℝ)*(sp14) + (2145270315931407/100000000000000 : ℝ)*(sp15) + (2145316360394531/100000000000000 : ℝ)*(f.failure) + (1104240073601729/25000000000000 : ℝ)*(f.sum) + (84123090156319/36660000000000000000000000000 : ℝ)*base66 + (2519843371321824059/1833000000000000000000000000000000 : ℝ)*base68 + (107442233179543681/35250000000000000000000000000000 : ℝ)*base70 + (11460542693512824059/1833000000000000000000000000000000 : ℝ)*base72 + (96237700049419/36660000000000000000000000000 : ℝ)*base74 + (97430337757456319/35250000000000000000000000000000 : ℝ)*base75 + (7880522011747991353/611000000000000000000000000000000 : ℝ)*base78 + (16520050064864991353/611000000000000000000000000000000 : ℝ)*base80 + (387176429547/6110000000000000000000000000 : ℝ)*base82 + (8837439/10000000000000000000000 : ℝ)*base89 + (8837439/10000000000000000000000 : ℝ)*base91 + (91162561/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1280_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29411/50000 : ℝ) else (79583/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84107/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1280_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1280_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29411/50000 : ℝ) else (79583/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84107/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1280_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4239/1024 : ℝ) ≤ p) (hpb : p ≤ (265/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152290869/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14663/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10997/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15709/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(29411/50000 : ℝ) else (79583/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84107/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1280_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
