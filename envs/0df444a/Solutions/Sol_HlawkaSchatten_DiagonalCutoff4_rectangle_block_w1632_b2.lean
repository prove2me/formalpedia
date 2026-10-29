-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1632_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:07.469689+00:00
-- url     : https://prove2.me/submissions/a04c1dc4-7289-42db-908a-950778f33898

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
theorem support_rectangle_w1632_box_0 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1385825169/10000000000 : ℝ)*x 0 + (84570787/156250000 : ℝ)*x 1 + (5412530361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1385825169/10000000000 : ℝ)^4847 ≤ (81623070849/1000000000000 : ℝ)^3823 := by
    have hnat : (1385825169 : ℕ)^4847*1000000000000^3823 ≤ 81623070849^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1385825169 10000000000 81623070849 1000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84570787/156250000 : ℝ)^4847 ≤ (45918846486537/100000000000000 : ℝ)^3823 := by
    have hnat : (84570787 : ℕ)^4847*100000000000000^3823 ≤ 45918846486537^3823*156250000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84570787 156250000 45918846486537 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412530361/10000000000 : ℝ)^4847 ≤ (45918846411243/100000000000000 : ℝ)^3823 := by
    have hnat : (5412530361 : ℕ)^4847*100000000000000^3823 ≤ 45918846411243^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412530361 10000000000 45918846411243 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1385825169/10000000000 : ℝ), (84570787/156250000 : ℝ), (5412530361/10000000000 : ℝ)] ![(81623070849/1000000000000 : ℝ), (45918846486537/100000000000000 : ℝ), (45918846411243/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1385825169/10000000000 : ℝ)|^4847 ≤ (81623070849/1000000000000 : ℝ)^3823
        have hw : |(-1385825169/10000000000 : ℝ)|=(1385825169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84570787/156250000 : ℝ)|^4847 ≤ (45918846486537/100000000000000 : ℝ)^3823
        have hw : |(84570787/156250000 : ℝ)|=(84570787/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412530361/10000000000 : ℝ)|^4847 ≤ (45918846411243/100000000000000 : ℝ)^3823
        have hw : |(5412530361/10000000000 : ℝ)|=(5412530361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_1 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164101399/312500000 : ℝ)*x 0 + (-1612431111/10000000000 : ℝ)*x 1 + (5412530463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164101399/312500000 : ℝ)^4847 ≤ (4419099876453/10000000000000 : ℝ)^3823 := by
    have hnat : (164101399 : ℕ)^4847*10000000000000^3823 ≤ 4419099876453^3823*312500000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164101399 312500000 4419099876453 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1612431111/10000000000 : ℝ)^4847 ≤ (2472538426509/25000000000000 : ℝ)^3823 := by
    have hnat : (1612431111 : ℕ)^4847*25000000000000^3823 ≤ 2472538426509^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1612431111 10000000000 2472538426509 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412530463/10000000000 : ℝ)^4847 ≤ (45918847508377/100000000000000 : ℝ)^3823 := by
    have hnat : (5412530463 : ℕ)^4847*100000000000000^3823 ≤ 45918847508377^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412530463 10000000000 45918847508377 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164101399/312500000 : ℝ), (-1612431111/10000000000 : ℝ), (5412530463/10000000000 : ℝ)] ![(4419099876453/10000000000000 : ℝ), (2472538426509/25000000000000 : ℝ), (45918847508377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164101399/312500000 : ℝ)|^4847 ≤ (4419099876453/10000000000000 : ℝ)^3823
        have hw : |(164101399/312500000 : ℝ)|=(164101399/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1612431111/10000000000 : ℝ)|^4847 ≤ (2472538426509/25000000000000 : ℝ)^3823
        have hw : |(-1612431111/10000000000 : ℝ)|=(1612431111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412530463/10000000000 : ℝ)|^4847 ≤ (45918847508377/100000000000000 : ℝ)^3823
        have hw : |(5412530463/10000000000 : ℝ)|=(5412530463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_2 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164101401/312500000 : ℝ)*x 0 + (2706265211/5000000000 : ℝ)*x 1 + (-806215541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164101401/312500000 : ℝ)^4847 ≤ (11047749861843/25000000000000 : ℝ)^3823 := by
    have hnat : (164101401 : ℕ)^4847*25000000000000^3823 ≤ 11047749861843^3823*312500000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164101401 312500000 11047749861843 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706265211/5000000000 : ℝ)^4847 ≤ (11479711766843/25000000000000 : ℝ)^3823 := by
    have hnat : (2706265211 : ℕ)^4847*25000000000000^3823 ≤ 11479711766843^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706265211 5000000000 11479711766843 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806215541/5000000000 : ℝ)^4847 ≤ (4945076740257/50000000000000 : ℝ)^3823 := by
    have hnat : (806215541 : ℕ)^4847*50000000000000^3823 ≤ 4945076740257^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806215541 5000000000 4945076740257 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164101401/312500000 : ℝ), (2706265211/5000000000 : ℝ), (-806215541/5000000000 : ℝ)] ![(11047749861843/25000000000000 : ℝ), (11479711766843/25000000000000 : ℝ), (4945076740257/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164101401/312500000 : ℝ)|^4847 ≤ (11047749861843/25000000000000 : ℝ)^3823
        have hw : |(164101401/312500000 : ℝ)|=(164101401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706265211/5000000000 : ℝ)|^4847 ≤ (11479711766843/25000000000000 : ℝ)^3823
        have hw : |(2706265211/5000000000 : ℝ)|=(2706265211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-806215541/5000000000 : ℝ)|^4847 ≤ (4945076740257/50000000000000 : ℝ)^3823
        have hw : |(-806215541/5000000000 : ℝ)|=(806215541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_3 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4472847327/10000000000 : ℝ)*x 0 + (4068065751/10000000000 : ℝ)*x 1 + (2034032887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4472847327/10000000000 : ℝ)^4847 ≤ (3605721298107/10000000000000 : ℝ)^3823 := by
    have hnat : (4472847327 : ℕ)^4847*10000000000000^3823 ≤ 3605721298107^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4472847327 10000000000 3605721298107 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4068065751/10000000000 : ℝ)^4847 ≤ (31971393385187/100000000000000 : ℝ)^3823 := by
    have hnat : (4068065751 : ℕ)^4847*100000000000000^3823 ≤ 31971393385187^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4068065751 10000000000 31971393385187 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2034032887/5000000000 : ℝ)^4847 ≤ (7992848403591/25000000000000 : ℝ)^3823 := by
    have hnat : (2034032887 : ℕ)^4847*25000000000000^3823 ≤ 7992848403591^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034032887 5000000000 7992848403591 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4472847327/10000000000 : ℝ), (4068065751/10000000000 : ℝ), (2034032887/5000000000 : ℝ)] ![(3605721298107/10000000000000 : ℝ), (31971393385187/100000000000000 : ℝ), (7992848403591/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4472847327/10000000000 : ℝ)|^4847 ≤ (3605721298107/10000000000000 : ℝ)^3823
        have hw : |(4472847327/10000000000 : ℝ)|=(4472847327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4068065751/10000000000 : ℝ)|^4847 ≤ (31971393385187/100000000000000 : ℝ)^3823
        have hw : |(4068065751/10000000000 : ℝ)|=(4068065751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2034032887/5000000000 : ℝ)|^4847 ≤ (7992848403591/25000000000000 : ℝ)^3823
        have hw : |(2034032887/5000000000 : ℝ)|=(2034032887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_4 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-962868543/5000000000 : ℝ)*x 0 + (5215162869/10000000000 : ℝ)*x 1 + (2607581353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (962868543/5000000000 : ℝ)^4847 ≤ (123872393903/1000000000000 : ℝ)^3823 := by
    have hnat : (962868543 : ℕ)^4847*1000000000000^3823 ≤ 123872393903^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      962868543 5000000000 123872393903 1000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215162869/10000000000 : ℝ)^4847 ≤ (1368949411233/3125000000000 : ℝ)^3823 := by
    have hnat : (5215162869 : ℕ)^4847*3125000000000^3823 ≤ 1368949411233^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215162869 10000000000 1368949411233 3125000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2607581353/5000000000 : ℝ)^4847 ≤ (684474678493/1562500000000 : ℝ)^3823 := by
    have hnat : (2607581353 : ℕ)^4847*1562500000000^3823 ≤ 684474678493^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607581353 5000000000 684474678493 1562500000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-962868543/5000000000 : ℝ), (5215162869/10000000000 : ℝ), (2607581353/5000000000 : ℝ)] ![(123872393903/1000000000000 : ℝ), (1368949411233/3125000000000 : ℝ), (684474678493/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-962868543/5000000000 : ℝ)|^4847 ≤ (123872393903/1000000000000 : ℝ)^3823
        have hw : |(-962868543/5000000000 : ℝ)|=(962868543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215162869/10000000000 : ℝ)|^4847 ≤ (1368949411233/3125000000000 : ℝ)^3823
        have hw : |(5215162869/10000000000 : ℝ)|=(5215162869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2607581353/5000000000 : ℝ)|^4847 ≤ (684474678493/1562500000000 : ℝ)^3823
        have hw : |(2607581353/5000000000 : ℝ)|=(2607581353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_5 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387045329/10000000000 : ℝ)*x 0 + (-42413409/250000000 : ℝ)*x 1 + (5215163037/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387045329/10000000000 : ℝ)^4847 ≤ (4564489706861/10000000000000 : ℝ)^3823 := by
    have hnat : (5387045329 : ℕ)^4847*10000000000000^3823 ≤ 4564489706861^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387045329 10000000000 4564489706861 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42413409/250000000 : ℝ)^4847 ≤ (5274359978163/50000000000000 : ℝ)^3823 := by
    have hnat : (42413409 : ℕ)^4847*50000000000000^3823 ≤ 5274359978163^3823*250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42413409 250000000 5274359978163 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215163037/10000000000 : ℝ)^4847 ≤ (43806382948609/100000000000000 : ℝ)^3823 := by
    have hnat : (5215163037 : ℕ)^4847*100000000000000^3823 ≤ 43806382948609^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215163037 10000000000 43806382948609 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387045329/10000000000 : ℝ), (-42413409/250000000 : ℝ), (5215163037/10000000000 : ℝ)] ![(4564489706861/10000000000000 : ℝ), (5274359978163/50000000000000 : ℝ), (43806382948609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387045329/10000000000 : ℝ)|^4847 ≤ (4564489706861/10000000000000 : ℝ)^3823
        have hw : |(5387045329/10000000000 : ℝ)|=(5387045329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42413409/250000000 : ℝ)|^4847 ≤ (5274359978163/50000000000000 : ℝ)^3823
        have hw : |(-42413409/250000000 : ℝ)|=(42413409/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215163037/10000000000 : ℝ)|^4847 ≤ (43806382948609/100000000000000 : ℝ)^3823
        have hw : |(5215163037/10000000000 : ℝ)|=(5215163037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_6 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077409113/2000000000 : ℝ)*x 0 + (2607581387/5000000000 : ℝ)*x 1 + (-424134099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077409113/2000000000 : ℝ)^4847 ≤ (45644899603869/100000000000000 : ℝ)^3823 := by
    have hnat : (1077409113 : ℕ)^4847*100000000000000^3823 ≤ 45644899603869^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077409113 2000000000 45644899603869 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607581387/5000000000 : ℝ)^4847 ≤ (43806380147733/100000000000000 : ℝ)^3823 := by
    have hnat : (2607581387 : ℕ)^4847*100000000000000^3823 ≤ 43806380147733^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607581387 5000000000 43806380147733 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424134099/2500000000 : ℝ)^4847 ≤ (10548720240123/100000000000000 : ℝ)^3823 := by
    have hnat : (424134099 : ℕ)^4847*100000000000000^3823 ≤ 10548720240123^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424134099 2500000000 10548720240123 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077409113/2000000000 : ℝ), (2607581387/5000000000 : ℝ), (-424134099/2500000000 : ℝ)] ![(45644899603869/100000000000000 : ℝ), (43806380147733/100000000000000 : ℝ), (10548720240123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077409113/2000000000 : ℝ)|^4847 ≤ (45644899603869/100000000000000 : ℝ)^3823
        have hw : |(1077409113/2000000000 : ℝ)|=(1077409113/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607581387/5000000000 : ℝ)|^4847 ≤ (43806380147733/100000000000000 : ℝ)^3823
        have hw : |(2607581387/5000000000 : ℝ)|=(2607581387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424134099/2500000000 : ℝ)|^4847 ≤ (10548720240123/100000000000000 : ℝ)^3823
        have hw : |(-424134099/2500000000 : ℝ)|=(424134099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_7 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (391047403/1000000000 : ℝ)*x 0 + (4348919657/10000000000 : ℝ)*x 1 + (4348919551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (391047403/1000000000 : ℝ)^4847 ≤ (30409343507049/100000000000000 : ℝ)^3823 := by
    have hnat : (391047403 : ℕ)^4847*100000000000000^3823 ≤ 30409343507049^3823*1000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391047403 1000000000 30409343507049 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4348919657/10000000000 : ℝ)^4847 ≤ (17397664387837/50000000000000 : ℝ)^3823 := by
    have hnat : (4348919657 : ℕ)^4847*50000000000000^3823 ≤ 17397664387837^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348919657 10000000000 17397664387837 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4348919551/10000000000 : ℝ)^4847 ≤ (8698831925103/25000000000000 : ℝ)^3823 := by
    have hnat : (4348919551 : ℕ)^4847*25000000000000^3823 ≤ 8698831925103^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4348919551 10000000000 8698831925103 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(391047403/1000000000 : ℝ), (4348919657/10000000000 : ℝ), (4348919551/10000000000 : ℝ)] ![(30409343507049/100000000000000 : ℝ), (17397664387837/50000000000000 : ℝ), (8698831925103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(391047403/1000000000 : ℝ)|^4847 ≤ (30409343507049/100000000000000 : ℝ)^3823
        have hw : |(391047403/1000000000 : ℝ)|=(391047403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4348919657/10000000000 : ℝ)|^4847 ≤ (17397664387837/50000000000000 : ℝ)^3823
        have hw : |(4348919657/10000000000 : ℝ)|=(4348919657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4348919551/10000000000 : ℝ)|^4847 ≤ (8698831925103/25000000000000 : ℝ)^3823
        have hw : |(4348919551/10000000000 : ℝ)|=(4348919551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_8 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-181072573/1000000000 : ℝ)*x 0 + (5073649519/10000000000 : ℝ)*x 1 + (5442207557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181072573/1000000000 : ℝ)^4847 ≤ (5728444121873/50000000000000 : ℝ)^3823 := by
    have hnat : (181072573 : ℕ)^4847*50000000000000^3823 ≤ 5728444121873^3823*1000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181072573 1000000000 5728444121873 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5073649519/10000000000 : ℝ)^4847 ≤ (42304817039887/100000000000000 : ℝ)^3823 := by
    have hnat : (5073649519 : ℕ)^4847*100000000000000^3823 ≤ 42304817039887^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5073649519 10000000000 42304817039887 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5442207557/10000000000 : ℝ)^4847 ≤ (23119147355489/50000000000000 : ℝ)^3823 := by
    have hnat : (5442207557 : ℕ)^4847*50000000000000^3823 ≤ 23119147355489^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442207557 10000000000 23119147355489 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-181072573/1000000000 : ℝ), (5073649519/10000000000 : ℝ), (5442207557/10000000000 : ℝ)] ![(5728444121873/50000000000000 : ℝ), (42304817039887/100000000000000 : ℝ), (23119147355489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-181072573/1000000000 : ℝ)|^4847 ≤ (5728444121873/50000000000000 : ℝ)^3823
        have hw : |(-181072573/1000000000 : ℝ)|=(181072573/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5073649519/10000000000 : ℝ)|^4847 ≤ (42304817039887/100000000000000 : ℝ)^3823
        have hw : |(5073649519/10000000000 : ℝ)|=(5073649519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5442207557/10000000000 : ℝ)|^4847 ≤ (23119147355489/50000000000000 : ℝ)^3823
        have hw : |(5442207557/10000000000 : ℝ)|=(5442207557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_9 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2615411811/5000000000 : ℝ)*x 0 + (-319868243/2000000000 : ℝ)*x 1 + (2721104007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2615411811/5000000000 : ℝ)^4847 ≤ (43973230832893/100000000000000 : ℝ)^3823 := by
    have hnat : (2615411811 : ℕ)^4847*100000000000000^3823 ≤ 43973230832893^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615411811 5000000000 43973230832893 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319868243/2000000000 : ℝ)^4847 ≤ (9788469520119/100000000000000 : ℝ)^3823 := by
    have hnat : (319868243 : ℕ)^4847*100000000000000^3823 ≤ 9788469520119^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319868243 2000000000 9788469520119 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721104007/5000000000 : ℝ)^4847 ≤ (11559574908443/25000000000000 : ℝ)^3823 := by
    have hnat : (2721104007 : ℕ)^4847*25000000000000^3823 ≤ 11559574908443^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721104007 5000000000 11559574908443 25000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2615411811/5000000000 : ℝ), (-319868243/2000000000 : ℝ), (2721104007/5000000000 : ℝ)] ![(43973230832893/100000000000000 : ℝ), (9788469520119/100000000000000 : ℝ), (11559574908443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2615411811/5000000000 : ℝ)|^4847 ≤ (43973230832893/100000000000000 : ℝ)^3823
        have hw : |(2615411811/5000000000 : ℝ)|=(2615411811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-319868243/2000000000 : ℝ)|^4847 ≤ (9788469520119/100000000000000 : ℝ)^3823
        have hw : |(-319868243/2000000000 : ℝ)|=(319868243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721104007/5000000000 : ℝ)|^4847 ≤ (11559574908443/25000000000000 : ℝ)^3823
        have hw : |(2721104007/5000000000 : ℝ)|=(2721104007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_10 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (209232959/400000000 : ℝ)*x 0 + (5442208003/10000000000 : ℝ)*x 1 + (-319868149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (209232959/400000000 : ℝ)^4847 ≤ (8794646919053/20000000000000 : ℝ)^3823 := by
    have hnat : (209232959 : ℕ)^4847*20000000000000^3823 ≤ 8794646919053^3823*400000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209232959 400000000 8794646919053 20000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5442208003/10000000000 : ℝ)^4847 ≤ (577978743941/1250000000000 : ℝ)^3823 := by
    have hnat : (5442208003 : ℕ)^4847*1250000000000^3823 ≤ 577978743941^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5442208003 10000000000 577978743941 1250000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319868149/2000000000 : ℝ)^4847 ≤ (9788465873081/100000000000000 : ℝ)^3823 := by
    have hnat : (319868149 : ℕ)^4847*100000000000000^3823 ≤ 9788465873081^3823*2000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319868149 2000000000 9788465873081 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(209232959/400000000 : ℝ), (5442208003/10000000000 : ℝ), (-319868149/2000000000 : ℝ)] ![(8794646919053/20000000000000 : ℝ), (577978743941/1250000000000 : ℝ), (9788465873081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(209232959/400000000 : ℝ)|^4847 ≤ (8794646919053/20000000000000 : ℝ)^3823
        have hw : |(209232959/400000000 : ℝ)|=(209232959/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5442208003/10000000000 : ℝ)|^4847 ≤ (577978743941/1250000000000 : ℝ)^3823
        have hw : |(5442208003/10000000000 : ℝ)|=(5442208003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-319868149/2000000000 : ℝ)|^4847 ≤ (9788465873081/100000000000000 : ℝ)^3823
        have hw : |(-319868149/2000000000 : ℝ)|=(319868149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_11 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (56937781/125000000 : ℝ)*x 0 + (402575913/1000000000 : ℝ)*x 1 + (161030319/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56937781/125000000 : ℝ)^4847 ≤ (18449575235169/50000000000000 : ℝ)^3823 := by
    have hnat : (56937781 : ℕ)^4847*50000000000000^3823 ≤ 18449575235169^3823*125000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56937781 125000000 18449575235169 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402575913/1000000000 : ℝ)^4847 ≤ (31550430492897/100000000000000 : ℝ)^3823 := by
    have hnat : (402575913 : ℕ)^4847*100000000000000^3823 ≤ 31550430492897^3823*1000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402575913 1000000000 31550430492897 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161030319/400000000 : ℝ)^4847 ≤ (3155041901643/10000000000000 : ℝ)^3823 := by
    have hnat : (161030319 : ℕ)^4847*10000000000000^3823 ≤ 3155041901643^3823*400000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161030319 400000000 3155041901643 10000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(56937781/125000000 : ℝ), (402575913/1000000000 : ℝ), (161030319/400000000 : ℝ)] ![(18449575235169/50000000000000 : ℝ), (31550430492897/100000000000000 : ℝ), (3155041901643/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(56937781/125000000 : ℝ)|^4847 ≤ (18449575235169/50000000000000 : ℝ)^3823
        have hw : |(56937781/125000000 : ℝ)|=(56937781/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402575913/1000000000 : ℝ)|^4847 ≤ (31550430492897/100000000000000 : ℝ)^3823
        have hw : |(402575913/1000000000 : ℝ)|=(402575913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161030319/400000000 : ℝ)|^4847 ≤ (3155041901643/10000000000000 : ℝ)^3823
        have hw : |(161030319/400000000 : ℝ)|=(161030319/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_12 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-749650823/5000000000 : ℝ)*x 0 + (693561037/1250000000 : ℝ)*x 1 + (5195310737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749650823/5000000000 : ℝ)^4847 ≤ (450940101681/5000000000000 : ℝ)^3823 := by
    have hnat : (749650823 : ℕ)^4847*5000000000000^3823 ≤ 450940101681^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749650823 5000000000 450940101681 5000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (693561037/1250000000 : ℝ)^4847 ≤ (47386128565701/100000000000000 : ℝ)^3823 := by
    have hnat : (693561037 : ℕ)^4847*100000000000000^3823 ≤ 47386128565701^3823*1250000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693561037 1250000000 47386128565701 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5195310737/10000000000 : ℝ)^4847 ≤ (43595069379087/100000000000000 : ℝ)^3823 := by
    have hnat : (5195310737 : ℕ)^4847*100000000000000^3823 ≤ 43595069379087^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195310737 10000000000 43595069379087 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-749650823/5000000000 : ℝ), (693561037/1250000000 : ℝ), (5195310737/10000000000 : ℝ)] ![(450940101681/5000000000000 : ℝ), (47386128565701/100000000000000 : ℝ), (43595069379087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-749650823/5000000000 : ℝ)|^4847 ≤ (450940101681/5000000000000 : ℝ)^3823
        have hw : |(-749650823/5000000000 : ℝ)|=(749650823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(693561037/1250000000 : ℝ)|^4847 ≤ (47386128565701/100000000000000 : ℝ)^3823
        have hw : |(693561037/1250000000 : ℝ)|=(693561037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5195310737/10000000000 : ℝ)|^4847 ≤ (43595069379087/100000000000000 : ℝ)^3823
        have hw : |(5195310737/10000000000 : ℝ)|=(5195310737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_13 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5400713013/10000000000 : ℝ)*x 0 + (-852352319/5000000000 : ℝ)*x 1 + (519531101/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400713013/10000000000 : ℝ)^4847 ≤ (45791773700699/100000000000000 : ℝ)^3823 := by
    have hnat : (5400713013 : ℕ)^4847*100000000000000^3823 ≤ 45791773700699^3823*10000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400713013 10000000000 45791773700699 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852352319/5000000000 : ℝ)^4847 ≤ (10613154008263/100000000000000 : ℝ)^3823 := by
    have hnat : (852352319 : ℕ)^4847*100000000000000^3823 ≤ 10613154008263^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852352319 5000000000 10613154008263 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519531101/1000000000 : ℝ)^4847 ≤ (43595072283493/100000000000000 : ℝ)^3823 := by
    have hnat : (519531101 : ℕ)^4847*100000000000000^3823 ≤ 43595072283493^3823*1000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519531101 1000000000 43595072283493 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400713013/10000000000 : ℝ), (-852352319/5000000000 : ℝ), (519531101/1000000000 : ℝ)] ![(45791773700699/100000000000000 : ℝ), (10613154008263/100000000000000 : ℝ), (43595072283493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400713013/10000000000 : ℝ)|^4847 ≤ (45791773700699/100000000000000 : ℝ)^3823
        have hw : |(5400713013/10000000000 : ℝ)|=(5400713013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-852352319/5000000000 : ℝ)|^4847 ≤ (10613154008263/100000000000000 : ℝ)^3823
        have hw : |(-852352319/5000000000 : ℝ)|=(852352319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519531101/1000000000 : ℝ)|^4847 ≤ (43595072283493/100000000000000 : ℝ)^3823
        have hw : |(519531101/1000000000 : ℝ)|=(519531101/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_14 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1350178319/2500000000 : ℝ)*x 0 + (2597655277/5000000000 : ℝ)*x 1 + (-852352447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1350178319/2500000000 : ℝ)^4847 ≤ (45791776527927/100000000000000 : ℝ)^3823 := by
    have hnat : (1350178319 : ℕ)^4847*100000000000000^3823 ≤ 45791776527927^3823*2500000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350178319 2500000000 45791776527927 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2597655277/5000000000 : ℝ)^4847 ≤ (21797533716089/50000000000000 : ℝ)^3823 := by
    have hnat : (2597655277 : ℕ)^4847*50000000000000^3823 ≤ 21797533716089^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597655277 5000000000 21797533716089 50000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (852352447/5000000000 : ℝ)^4847 ≤ (10613156028973/100000000000000 : ℝ)^3823 := by
    have hnat : (852352447 : ℕ)^4847*100000000000000^3823 ≤ 10613156028973^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852352447 5000000000 10613156028973 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1350178319/2500000000 : ℝ), (2597655277/5000000000 : ℝ), (-852352447/5000000000 : ℝ)] ![(45791776527927/100000000000000 : ℝ), (21797533716089/50000000000000 : ℝ), (10613156028973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1350178319/2500000000 : ℝ)|^4847 ≤ (45791776527927/100000000000000 : ℝ)^3823
        have hw : |(1350178319/2500000000 : ℝ)|=(1350178319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2597655277/5000000000 : ℝ)|^4847 ≤ (21797533716089/50000000000000 : ℝ)^3823
        have hw : |(2597655277/5000000000 : ℝ)|=(2597655277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-852352447/5000000000 : ℝ)|^4847 ≤ (10613156028973/100000000000000 : ℝ)^3823
        have hw : |(-852352447/5000000000 : ℝ)|=(852352447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1632_box_15 (p : ℝ) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1926141101/5000000000 : ℝ)*x 0 + (2188559183/5000000000 : ℝ)*x 1 + (5471397/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1926141101/5000000000 : ℝ)^4847 ≤ (29836760050983/100000000000000 : ℝ)^3823 := by
    have hnat : (1926141101 : ℕ)^4847*100000000000000^3823 ≤ 29836760050983^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926141101 5000000000 29836760050983 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2188559183/5000000000 : ℝ)^4847 ≤ (35081623855897/100000000000000 : ℝ)^3823 := by
    have hnat : (2188559183 : ℕ)^4847*100000000000000^3823 ≤ 35081623855897^3823*5000000000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188559183 5000000000 35081623855897 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5471397/12500000 : ℝ)^4847 ≤ (35081616072147/100000000000000 : ℝ)^3823 := by
    have hnat : (5471397 : ℕ)^4847*100000000000000^3823 ≤ 35081616072147^3823*12500000^4847 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471397 12500000 35081616072147 100000000000000 4847 3823 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4847/1024 : ℝ)) 4847 3823 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1926141101/5000000000 : ℝ), (2188559183/5000000000 : ℝ), (5471397/12500000 : ℝ)] ![(29836760050983/100000000000000 : ℝ), (35081623855897/100000000000000 : ℝ), (35081616072147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1926141101/5000000000 : ℝ)|^4847 ≤ (29836760050983/100000000000000 : ℝ)^3823
        have hw : |(1926141101/5000000000 : ℝ)|=(1926141101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2188559183/5000000000 : ℝ)|^4847 ≤ (35081623855897/100000000000000 : ℝ)^3823
        have hw : |(2188559183/5000000000 : ℝ)|=(2188559183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5471397/12500000 : ℝ)|^4847 ≤ (35081616072147/100000000000000 : ℝ)^3823
        have hw : |(5471397/12500000 : ℝ)|=(5471397/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1632_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2643/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16249/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1826/3125 : ℝ) ∧ (40431/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (44023/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8151/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2643/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8151/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2643/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8151/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2643/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8151/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2643/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8151/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2643/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8151/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2643/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2643/25000 : ℝ) ^ (4843/1024 : ℝ) ≤ (485052649814083/20000000000000000000 : ℝ) := by
    have hpowers : (2643/25000 : ℝ)^4843 ≤ (485052649814083/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2643 : ℕ)^4843*20000000000000000000^1024 ≤ 485052649814083^1024*25000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2643 25000 485052649814083 20000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2643/25000 : ℝ)) (X := (485052649814083/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8151/50000 : ℝ) ^ (4843/1024 : ℝ) ≤ (18806130175409311/100000000000000000000 : ℝ) := by
    have hpowers : (8151/50000 : ℝ)^4843 ≤ (18806130175409311/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8151 : ℕ)^4843*100000000000000000000^1024 ≤ 18806130175409311^1024*50000^4843 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8151 50000 18806130175409311 100000000000000000000 4843 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8151/50000 : ℝ)) (X := (18806130175409311/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000485052649814083/10000000000000000000 : ℝ) ≤ (5000051278589157/5000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (10000485052649814083/10000000000000000000 : ℝ)^1024 ≤ (5000051278589157/5000000000000000 : ℝ)^4843 := by
      have hnat : (10000485052649814083 : ℕ)^1024*5000000000000000^4843 ≤ 5000051278589157^4843*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000485052649814083 10000000000000000000 5000051278589157 5000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000051278589157/5000000000000000 : ℝ)) (X := (10000485052649814083/10000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010615696712239863/50000000000000000000 : ℝ) ≤ (10000448877289609/10000000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50010615696712239863/50000000000000000000 : ℝ)^1024 ≤ (10000448877289609/10000000000000000 : ℝ)^4843 := by
      have hnat : (50010615696712239863 : ℕ)^1024*10000000000000000^4843 ≤ 10000448877289609^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010615696712239863 50000000000000000000 10000448877289609 10000000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000448877289609/10000000000000000 : ℝ)) (X := (50010615696712239863/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018806130175409311/50000000000000000000 : ℝ) ≤ (1250099399675113/1250000000000000 : ℝ) ^ (4843/1024 : ℝ) := by
    have hpowers : (50018806130175409311/50000000000000000000 : ℝ)^1024 ≤ (1250099399675113/1250000000000000 : ℝ)^4843 := by
      have hnat : (50018806130175409311 : ℕ)^1024*1250000000000000^4843 ≤ 1250099399675113^4843*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018806130175409311 50000000000000000000 1250099399675113 1250000000000000 1024 4843 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250099399675113/1250000000000000 : ℝ)) (X := (50018806130175409311/50000000000000000000 : ℝ)) (by norm_num) 4843 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(485052649814083/20000000000000000000 : ℝ) ≤ ((954887751003308629/955000000000000000 : ℝ)+2*(69264022259/114600000000000 : ℝ)*(2643/25000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (954887751003308629/955000000000000000 : ℝ)+2*(69264022259/114600000000000 : ℝ)*(2643/25000 : ℝ)=(5000051278589157/5000000000000000 : ℝ) by norm_num, show 1+2*(485052649814083/20000000000000000000 : ℝ)=(10000485052649814083/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18806130175409311/100000000000000000000 : ℝ)+(485052649814083/20000000000000000000 : ℝ) ≤ ((954887751003308629/955000000000000000 : ℝ)+(69264022259/114600000000000 : ℝ)*((8151/50000 : ℝ)+(2643/25000 : ℝ)))^(4843/1024 : ℝ) := by
    rw [show (954887751003308629/955000000000000000 : ℝ)+(69264022259/114600000000000 : ℝ)*((8151/50000 : ℝ)+(2643/25000 : ℝ))=(10000448877289609/10000000000000000 : ℝ) by norm_num, show 1+(18806130175409311/100000000000000000000 : ℝ)+(485052649814083/20000000000000000000 : ℝ)=(50010615696712239863/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18806130175409311/100000000000000000000 : ℝ) ≤ ((954887751003308629/955000000000000000 : ℝ)+2*(69264022259/114600000000000 : ℝ)*(8151/50000 : ℝ))^(4843/1024 : ℝ) := by
    rw [show (954887751003308629/955000000000000000 : ℝ)+2*(69264022259/114600000000000 : ℝ)*(8151/50000 : ℝ)=(1250099399675113/1250000000000000 : ℝ) by norm_num, show 1+2*(18806130175409311/100000000000000000000 : ℝ)=(50018806130175409311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (954887751003308629/955000000000000000 : ℝ)*(X 1 0+X 2 0)+(69264022259/114600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2643/25000 : ℝ)) (hi := (8151/50000 : ℝ)) (c := (954887751003308629/955000000000000000 : ℝ)) (alpha := (69264022259/114600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (954887751003308629/955000000000000000 : ℝ)*(X 0 1+X 2 1)+(69264022259/114600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2643/25000 : ℝ)) (hi := (8151/50000 : ℝ)) (c := (954887751003308629/955000000000000000 : ℝ)) (alpha := (69264022259/114600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (954887751003308629/955000000000000000 : ℝ)*(X 0 2+X 1 2)+(69264022259/114600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4843/1024 : ℝ)) (lo := (2643/25000 : ℝ)) (hi := (8151/50000 : ℝ)) (c := (954887751003308629/955000000000000000 : ℝ)) (alpha := (69264022259/114600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1385825169/10000000000 : ℝ)*X 0 0+(84570787/156250000 : ℝ)*X 0 1+(5412530361/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((164101399/312500000 : ℝ)*X 1 0+(-1612431111/10000000000 : ℝ)*X 1 1+(5412530463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((164101401/312500000 : ℝ)*X 2 0+(2706265211/5000000000 : ℝ)*X 2 1+(-806215541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4472847327/10000000000 : ℝ)*X 0 0+(4068065751/10000000000 : ℝ)*X 0 1+(2034032887/5000000000 : ℝ)*X 0 2+(4472847327/10000000000 : ℝ)*X 1 0+(4068065751/10000000000 : ℝ)*X 1 1+(2034032887/5000000000 : ℝ)*X 1 2+(4472847327/10000000000 : ℝ)*X 2 0+(4068065751/10000000000 : ℝ)*X 2 1+(2034032887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-962868543/5000000000 : ℝ)*X 0 0+(5215162869/10000000000 : ℝ)*X 0 1+(2607581353/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5387045329/10000000000 : ℝ)*X 1 0+(-42413409/250000000 : ℝ)*X 1 1+(5215163037/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1077409113/2000000000 : ℝ)*X 2 0+(2607581387/5000000000 : ℝ)*X 2 1+(-424134099/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((391047403/1000000000 : ℝ)*X 0 0+(4348919657/10000000000 : ℝ)*X 0 1+(4348919551/10000000000 : ℝ)*X 0 2+(391047403/1000000000 : ℝ)*X 1 0+(4348919657/10000000000 : ℝ)*X 1 1+(4348919551/10000000000 : ℝ)*X 1 2+(391047403/1000000000 : ℝ)*X 2 0+(4348919657/10000000000 : ℝ)*X 2 1+(4348919551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-181072573/1000000000 : ℝ)*X 0 0+(5073649519/10000000000 : ℝ)*X 0 1+(5442207557/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2615411811/5000000000 : ℝ)*X 1 0+(-319868243/2000000000 : ℝ)*X 1 1+(2721104007/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((209232959/400000000 : ℝ)*X 2 0+(5442208003/10000000000 : ℝ)*X 2 1+(-319868149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((56937781/125000000 : ℝ)*X 0 0+(402575913/1000000000 : ℝ)*X 0 1+(161030319/400000000 : ℝ)*X 0 2+(56937781/125000000 : ℝ)*X 1 0+(402575913/1000000000 : ℝ)*X 1 1+(161030319/400000000 : ℝ)*X 1 2+(56937781/125000000 : ℝ)*X 2 0+(402575913/1000000000 : ℝ)*X 2 1+(161030319/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-749650823/5000000000 : ℝ)*X 0 0+(693561037/1250000000 : ℝ)*X 0 1+(5195310737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5400713013/10000000000 : ℝ)*X 1 0+(-852352319/5000000000 : ℝ)*X 1 1+(519531101/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1350178319/2500000000 : ℝ)*X 2 0+(2597655277/5000000000 : ℝ)*X 2 1+(-852352447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1926141101/5000000000 : ℝ)*X 0 0+(2188559183/5000000000 : ℝ)*X 0 1+(5471397/12500000 : ℝ)*X 0 2+(1926141101/5000000000 : ℝ)*X 1 0+(2188559183/5000000000 : ℝ)*X 1 1+(5471397/12500000 : ℝ)*X 1 2+(1926141101/5000000000 : ℝ)*X 2 0+(2188559183/5000000000 : ℝ)*X 2 1+(5471397/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1632_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16249/25000 : ℝ) ≤ (-3879298398284910562101552318167/5968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1132191/5000000000000 : ℝ)*(lower2) + (9033653/100000000000000 : ℝ)*(lower3) + (6737597/100000000000000 : ℝ)*(lower5) + (215562824517853/12500000000000 : ℝ)*(major0) + (215562824517853/12500000000000 : ℝ)*(major1) + (215562824517853/12500000000000 : ℝ)*(major2) + (464657641/100000000000000 : ℝ)*(sp3) + (623311469325741/25000000000000 : ℝ)*(sp4) + (311652328810313/12500000000000 : ℝ)*(sp5) + (623311278498251/25000000000000 : ℝ)*(sp6) + (244355456593283/25000000000000 : ℝ)*(sp7) + (15176247/1000000000000 : ℝ)*(sp8) + (719111129/2500000000000 : ℝ)*(sp13) + (114046733/5000000000000 : ℝ)*(sp14) + (244355572757693/25000000000000 : ℝ)*(f.failure) + (155827962182979/6250000000000 : ℝ)*(f.sum) + (5031190865213/2865000000000000000000000000 : ℝ)*base65 + (83551805654901889/35812500000000000000000000000000 : ℝ)*base68 + (228102845810339389/35812500000000000000000000000000 : ℝ)*base70 + (277134710544651889/35812500000000000000000000000000 : ℝ)*base72 + (2599298840033/2865000000000000000000000000 : ℝ)*base73 + (295405196983589389/35812500000000000000000000000000 : ℝ)*base76 + (64533178435401889/35812500000000000000000000000000 : ℝ)*base78 + (303643674127401889/35812500000000000000000000000000 : ℝ)*base80 + (6218786214311/1432500000000000000000000000 : ℝ)*base82 + (10572803/2500000000000000000000 : ℝ)*base90 + (10572803/2500000000000000000000 : ℝ)*base92 + (10572803/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (1826/3125 : ℝ) ≤ (217986847765409678000461172739/373046875000000000000000000000 : ℝ) := by norm_num
    linear_combination (391631/5000000000000 : ℝ)*(upper0) + (267161/12500000000000 : ℝ)*(lower1) + (407199/2500000000000 : ℝ)*(upper4) + (56636626982413/3125000000000 : ℝ)*(major0) + (56636626982413/3125000000000 : ℝ)*(major1) + (56636626982413/3125000000000 : ℝ)*(major2) + (128902031078883/5000000000000 : ℝ)*(sp0) + (1289019731495673/50000000000000 : ℝ)*(sp1) + (1289019739283623/50000000000000 : ℝ)*(sp2) + (1027223717041107/100000000000000 : ℝ)*(sp3) + (1215491731/100000000000000 : ℝ)*(sp5) + (149989479/12500000000000 : ℝ)*(sp6) + (1674446943/100000000000000 : ℝ)*(sp7) + (28452709/50000000000000 : ℝ)*(sp8) + (20544507829761/2000000000000 : ℝ)*(f.failure) + (1289020339241539/50000000000000 : ℝ)*(f.sum) + (1095108535663/2865000000000000000000000000 : ℝ)*base66 + (10214479132305919/8953125000000000000000000000000 : ℝ)*base68 + (7198581085613897/4476562500000000000000000000000 : ℝ)*base70 + (19569203501805919/8953125000000000000000000000000 : ℝ)*base72 + (4632725657821/1432500000000000000000000000 : ℝ)*base73 + (18930477139600331/8953125000000000000000000000000 : ℝ)*base75 + (1592699980352693/1119140625000000000000000000000 : ℝ)*base78 + (102211496571850331/8953125000000000000000000000000 : ℝ)*base79 + (861224718017/2865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1591231/200000000000000000000 : ℝ)*base90 + (1591231/200000000000000000000 : ℝ)*base92 + (1591231/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (40431/50000 : ℝ) ≤ (1544513162307371022658567723/1910000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40809821/100000000000000 : ℝ)*(lower3) + (197420997/100000000000000 : ℝ)*(upper4) + (25900759/25000000000000 : ℝ)*(lower5) + (1911954220906963/100000000000000 : ℝ)*(major0) + (1911954220906963/100000000000000 : ℝ)*(major1) + (1911954220906963/100000000000000 : ℝ)*(major2) + (726177979/10000000000000 : ℝ)*(sp0) + (12264501/19531250000 : ℝ)*(sp1) + (112568746793/100000000000000 : ℝ)*(sp2) + (10898601381/25000000000000 : ℝ)*(sp3) + (2713279255905813/100000000000000 : ℝ)*(sp8) + (2713223723440483/100000000000000 : ℝ)*(sp9) + (271317394893881/10000000000000 : ℝ)*(sp10) + (1083623475232257/100000000000000 : ℝ)*(sp11) + (54183353481889/5000000000000 : ℝ)*(f.failure) + (678321629421401/25000000000000 : ℝ)*(f.sum) + (226487392577/5730000000000000000000000000 : ℝ)*base65 + (1515365058101176181/286500000000000000000000000000000 : ℝ)*base67 + (1890056047355323819/286500000000000000000000000000000 : ℝ)*base70 + (1013671558056676181/286500000000000000000000000000000 : ℝ)*base71 + (21380724513047/5730000000000000000000000000 : ℝ)*base73 + (1507202742726823819/286500000000000000000000000000000 : ℝ)*base76 + (165783602753323819/286500000000000000000000000000000 : ℝ)*base78 + (505075406922676181/286500000000000000000000000000000 : ℝ)*base79 + (29739882508333/5730000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4765919/500000000000000000000 : ℝ)*base90 + (4765919/500000000000000000000 : ℝ)*base92 + (4765919/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-44023/50000 : ℝ) ≤ (-2627562370828667028056339365431/2984375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48026599/100000000000000 : ℝ)*(upper1) + (1846841/50000000000000 : ℝ)*(lower2) + (116489007/100000000000000 : ℝ)*(upper3) + (49446639/100000000000000 : ℝ)*(upper5) + (61097195124831/3125000000000 : ℝ)*(major0) + (61097195124831/3125000000000 : ℝ)*(major1) + (61097195124831/3125000000000 : ℝ)*(major2) + (69545507/1562500000000 : ℝ)*(sp4) + (51781327639/100000000000000 : ℝ)*(sp6) + (2755916763/20000000000000 : ℝ)*(sp7) + (1415718385145291/50000000000000 : ℝ)*(sp12) + (283144122120303/10000000000000 : ℝ)*(sp13) + (44240459998053/1562500000000 : ℝ)*(sp14) + (1108113478778781/100000000000000 : ℝ)*(sp15) + (277031814590649/25000000000000 : ℝ)*(f.failure) + (283144122120303/10000000000000 : ℝ)*(f.sum) + (106631093683/59687500000000000000000000 : ℝ)*base65 + (85180812138591/46630859375000000000000000000 : ℝ)*base67 + (5261283397361963/1492187500000000000000000000000 : ℝ)*base70 + (7151636962072949/2984375000000000000000000000000 : ℝ)*base71 + (3277784500133/955000000000000000000000000 : ℝ)*base73 + (181842321055011/186523437500000000000000000000 : ℝ)*base76 + (4199889760111963/1492187500000000000000000000000 : ℝ)*base78 + (7700241733986963/1492187500000000000000000000000 : ℝ)*base80 + (1803832713673/955000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (11600121/2500000000000000000000 : ℝ)*base89 + (11600121/2500000000000000000000 : ℝ)*base91 + (11600121/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1632_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2643/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16249/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(1826/3125 : ℝ) else (40431/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44023/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1632_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1632_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2643/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16249/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(1826/3125 : ℝ) else (40431/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44023/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1632_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4843/1024 : ℝ) ≤ p) (hpb : p ≤ (4847/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (176433729/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8151/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2643/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16249/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(1826/3125 : ℝ) else (40431/50000 : ℝ) ≤ X j i ∧ X j i ≤ (44023/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1632_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
