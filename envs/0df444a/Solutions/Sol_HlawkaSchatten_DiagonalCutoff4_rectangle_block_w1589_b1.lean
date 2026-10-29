-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1589_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:36:54.246098+00:00
-- url     : https://prove2.me/submissions/fdc55d93-03cb-42ef-8410-1dbd190c31a2

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
theorem support_rectangle_w1589_s3_0 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-87989133/500000000 : ℝ)*x 0 + (5424728747/10000000000 : ℝ)*x 1 + (652431879/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87989133/500000000 : ℝ)^4675 ≤ (10810159366283/100000000000000 : ℝ)^3651 := by
    have hnat : (87989133 : ℕ)^4675*100000000000000^3651 ≤ 10810159366283^3651*500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87989133 500000000 10810159366283 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424728747/10000000000 : ℝ)^4675 ≤ (45696058217077/100000000000000 : ℝ)^3651 := by
    have hnat : (5424728747 : ℕ)^4675*100000000000000^3651 ≤ 45696058217077^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424728747 10000000000 45696058217077 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652431879/1250000000 : ℝ)^4675 ≤ (8698756479019/20000000000000 : ℝ)^3651 := by
    have hnat : (652431879 : ℕ)^4675*20000000000000^3651 ≤ 8698756479019^3651*1250000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652431879 1250000000 8698756479019 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87989133/500000000 : ℝ), (5424728747/10000000000 : ℝ), (652431879/1250000000 : ℝ)] ![(10810159366283/100000000000000 : ℝ), (45696058217077/100000000000000 : ℝ), (8698756479019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87989133/500000000 : ℝ)|^4675 ≤ (10810159366283/100000000000000 : ℝ)^3651
        have hw : |(-87989133/500000000 : ℝ)|=(87989133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424728747/10000000000 : ℝ)|^4675 ≤ (45696058217077/100000000000000 : ℝ)^3651
        have hw : |(5424728747/10000000000 : ℝ)|=(5424728747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652431879/1250000000 : ℝ)|^4675 ≤ (8698756479019/20000000000000 : ℝ)^3651
        have hw : |(652431879/1250000000 : ℝ)|=(652431879/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s3_1 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347364391/10000000000 : ℝ)*x 0 + (-466197933/2500000000 : ℝ)*x 1 + (41755641/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347364391/10000000000 : ℝ)^4675 ≤ (44863261560417/100000000000000 : ℝ)^3651 := by
    have hnat : (5347364391 : ℕ)^4675*100000000000000^3651 ≤ 44863261560417^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347364391 10000000000 44863261560417 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466197933/2500000000 : ℝ)^4675 ≤ (1164295502729/10000000000000 : ℝ)^3651 := by
    have hnat : (466197933 : ℕ)^4675*10000000000000^3651 ≤ 1164295502729^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466197933 2500000000 1164295502729 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41755641/80000000 : ℝ)^4675 ≤ (21746891693711/50000000000000 : ℝ)^3651 := by
    have hnat : (41755641 : ℕ)^4675*50000000000000^3651 ≤ 21746891693711^3651*80000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41755641 80000000 21746891693711 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347364391/10000000000 : ℝ), (-466197933/2500000000 : ℝ), (41755641/80000000 : ℝ)] ![(44863261560417/100000000000000 : ℝ), (1164295502729/10000000000000 : ℝ), (21746891693711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347364391/10000000000 : ℝ)|^4675 ≤ (44863261560417/100000000000000 : ℝ)^3651
        have hw : |(5347364391/10000000000 : ℝ)|=(5347364391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466197933/2500000000 : ℝ)|^4675 ≤ (1164295502729/10000000000000 : ℝ)^3651
        have hw : |(-466197933/2500000000 : ℝ)|=(466197933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41755641/80000000 : ℝ)|^4675 ≤ (21746891693711/50000000000000 : ℝ)^3651
        have hw : |(41755641/80000000 : ℝ)|=(41755641/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s3_2 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347364277/10000000000 : ℝ)*x 0 + (521945517/1000000000 : ℝ)*x 1 + (-1864791827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347364277/10000000000 : ℝ)^4675 ≤ (44863260335729/100000000000000 : ℝ)^3651 := by
    have hnat : (5347364277 : ℕ)^4675*100000000000000^3651 ≤ 44863260335729^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347364277 10000000000 44863260335729 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521945517/1000000000 : ℝ)^4675 ≤ (2174689193379/5000000000000 : ℝ)^3651 := by
    have hnat : (521945517 : ℕ)^4675*5000000000000^3651 ≤ 2174689193379^3651*1000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521945517 1000000000 2174689193379 5000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1864791827/10000000000 : ℝ)^4675 ≤ (2910738946697/25000000000000 : ℝ)^3651 := by
    have hnat : (1864791827 : ℕ)^4675*25000000000000^3651 ≤ 2910738946697^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1864791827 10000000000 2910738946697 25000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347364277/10000000000 : ℝ), (521945517/1000000000 : ℝ), (-1864791827/10000000000 : ℝ)] ![(44863260335729/100000000000000 : ℝ), (2174689193379/5000000000000 : ℝ), (2910738946697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347364277/10000000000 : ℝ)|^4675 ≤ (44863260335729/100000000000000 : ℝ)^3651
        have hw : |(5347364277/10000000000 : ℝ)|=(5347364277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(521945517/1000000000 : ℝ)|^4675 ≤ (2174689193379/5000000000000 : ℝ)^3651
        have hw : |(521945517/1000000000 : ℝ)|=(521945517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1864791827/10000000000 : ℝ)|^4675 ≤ (2910738946697/25000000000000 : ℝ)^3651
        have hw : |(-1864791827/10000000000 : ℝ)|=(1864791827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s3_3 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235088001/10000000000 : ℝ)*x 0 + (1997670317/5000000000 : ℝ)*x 1 + (89723603/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235088001/10000000000 : ℝ)^4675 ≤ (16640950919487/50000000000000 : ℝ)^3651 := by
    have hnat : (4235088001 : ℕ)^4675*50000000000000^3651 ≤ 16640950919487^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235088001 10000000000 16640950919487 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997670317/5000000000 : ℝ)^4675 ≤ (15444404744841/50000000000000 : ℝ)^3651 := by
    have hnat : (1997670317 : ℕ)^4675*50000000000000^3651 ≤ 15444404744841^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997670317 5000000000 15444404744841 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (89723603/200000000 : ℝ)^4675 ≤ (3582928865113/10000000000000 : ℝ)^3651 := by
    have hnat : (89723603 : ℕ)^4675*10000000000000^3651 ≤ 3582928865113^3651*200000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89723603 200000000 3582928865113 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235088001/10000000000 : ℝ), (1997670317/5000000000 : ℝ), (89723603/200000000 : ℝ)] ![(16640950919487/50000000000000 : ℝ), (15444404744841/50000000000000 : ℝ), (3582928865113/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235088001/10000000000 : ℝ)|^4675 ≤ (16640950919487/50000000000000 : ℝ)^3651
        have hw : |(4235088001/10000000000 : ℝ)|=(4235088001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1997670317/5000000000 : ℝ)|^4675 ≤ (15444404744841/50000000000000 : ℝ)^3651
        have hw : |(1997670317/5000000000 : ℝ)|=(1997670317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(89723603/200000000 : ℝ)|^4675 ≤ (3582928865113/10000000000000 : ℝ)^3651
        have hw : |(89723603/200000000 : ℝ)|=(89723603/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s3_4 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-879904513/5000000000 : ℝ)*x 0 + (1044108537/2000000000 : ℝ)*x 1 + (5423633509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (879904513/5000000000 : ℝ)^4675 ≤ (86482934051/800000000000 : ℝ)^3651 := by
    have hnat : (879904513 : ℕ)^4675*800000000000^3651 ≤ 86482934051^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879904513 5000000000 86482934051 800000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044108537/2000000000 : ℝ)^4675 ≤ (2175269409447/5000000000000 : ℝ)^3651 := by
    have hnat : (1044108537 : ℕ)^4675*5000000000000^3651 ≤ 2175269409447^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044108537 2000000000 2175269409447 5000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423633509/10000000000 : ℝ)^4675 ≤ (45684245040359/100000000000000 : ℝ)^3651 := by
    have hnat : (5423633509 : ℕ)^4675*100000000000000^3651 ≤ 45684245040359^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423633509 10000000000 45684245040359 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-879904513/5000000000 : ℝ), (1044108537/2000000000 : ℝ), (5423633509/10000000000 : ℝ)] ![(86482934051/800000000000 : ℝ), (2175269409447/5000000000000 : ℝ), (45684245040359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-879904513/5000000000 : ℝ)|^4675 ≤ (86482934051/800000000000 : ℝ)^3651
        have hw : |(-879904513/5000000000 : ℝ)|=(879904513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044108537/2000000000 : ℝ)|^4675 ≤ (2175269409447/5000000000000 : ℝ)^3651
        have hw : |(1044108537/2000000000 : ℝ)|=(1044108537/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423633509/10000000000 : ℝ)|^4675 ≤ (45684245040359/100000000000000 : ℝ)^3651
        have hw : |(5423633509/10000000000 : ℝ)|=(5423633509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s3_5 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264646807/500000000 : ℝ)*x 0 + (-66424513/400000000 : ℝ)*x 1 + (5423634781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264646807/500000000 : ℝ)^4675 ≤ (22139690946247/50000000000000 : ℝ)^3651 := by
    have hnat : (264646807 : ℕ)^4675*50000000000000^3651 ≤ 22139690946247^3651*500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264646807 500000000 22139690946247 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (66424513/400000000 : ℝ)^4675 ≤ (10036359325581/100000000000000 : ℝ)^3651 := by
    have hnat : (66424513 : ℕ)^4675*100000000000000^3651 ≤ 10036359325581^3651*400000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66424513 400000000 10036359325581 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423634781/10000000000 : ℝ)^4675 ≤ (45684258759693/100000000000000 : ℝ)^3651 := by
    have hnat : (5423634781 : ℕ)^4675*100000000000000^3651 ≤ 45684258759693^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423634781 10000000000 45684258759693 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264646807/500000000 : ℝ), (-66424513/400000000 : ℝ), (5423634781/10000000000 : ℝ)] ![(22139690946247/50000000000000 : ℝ), (10036359325581/100000000000000 : ℝ), (45684258759693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264646807/500000000 : ℝ)|^4675 ≤ (22139690946247/50000000000000 : ℝ)^3651
        have hw : |(264646807/500000000 : ℝ)|=(264646807/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-66424513/400000000 : ℝ)|^4675 ≤ (10036359325581/100000000000000 : ℝ)^3651
        have hw : |(-66424513/400000000 : ℝ)|=(66424513/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423634781/10000000000 : ℝ)|^4675 ≤ (45684258759693/100000000000000 : ℝ)^3651
        have hw : |(5423634781/10000000000 : ℝ)|=(5423634781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s3_6 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5292936447/10000000000 : ℝ)*x 0 + (5423633311/10000000000 : ℝ)*x 1 + (-1660614451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5292936447/10000000000 : ℝ)^4675 ≤ (44279385181109/100000000000000 : ℝ)^3651 := by
    have hnat : (5292936447 : ℕ)^4675*100000000000000^3651 ≤ 44279385181109^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292936447 10000000000 44279385181109 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423633311/10000000000 : ℝ)^4675 ≤ (45684242904803/100000000000000 : ℝ)^3651 := by
    have hnat : (5423633311 : ℕ)^4675*100000000000000^3651 ≤ 45684242904803^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423633311 10000000000 45684242904803 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1660614451/10000000000 : ℝ)^4675 ≤ (10036371908987/100000000000000 : ℝ)^3651 := by
    have hnat : (1660614451 : ℕ)^4675*100000000000000^3651 ≤ 10036371908987^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1660614451 10000000000 10036371908987 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5292936447/10000000000 : ℝ), (5423633311/10000000000 : ℝ), (-1660614451/10000000000 : ℝ)] ![(44279385181109/100000000000000 : ℝ), (45684242904803/100000000000000 : ℝ), (10036371908987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5292936447/10000000000 : ℝ)|^4675 ≤ (44279385181109/100000000000000 : ℝ)^3651
        have hw : |(5292936447/10000000000 : ℝ)|=(5292936447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423633311/10000000000 : ℝ)|^4675 ≤ (45684242904803/100000000000000 : ℝ)^3651
        have hw : |(5423633311/10000000000 : ℝ)|=(5423633311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1660614451/10000000000 : ℝ)|^4675 ≤ (10036371908987/100000000000000 : ℝ)^3651
        have hw : |(-1660614451/10000000000 : ℝ)|=(1660614451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s3_7 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235153753/10000000000 : ℝ)*x 0 + (896716333/2000000000 : ℝ)*x 1 + (3997957661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235153753/10000000000 : ℝ)^4675 ≤ (33282563484517/100000000000000 : ℝ)^3651 := by
    have hnat : (4235153753 : ℕ)^4675*100000000000000^3651 ≤ 33282563484517^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235153753 10000000000 33282563484517 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896716333/2000000000 : ℝ)^4675 ≤ (35802717143891/100000000000000 : ℝ)^3651 := by
    have hnat : (896716333 : ℕ)^4675*100000000000000^3651 ≤ 35802717143891^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896716333 2000000000 35802717143891 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3997957661/10000000000 : ℝ)^4675 ≤ (30914719359349/100000000000000 : ℝ)^3651 := by
    have hnat : (3997957661 : ℕ)^4675*100000000000000^3651 ≤ 30914719359349^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3997957661 10000000000 30914719359349 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235153753/10000000000 : ℝ), (896716333/2000000000 : ℝ), (3997957661/10000000000 : ℝ)] ![(33282563484517/100000000000000 : ℝ), (35802717143891/100000000000000 : ℝ), (30914719359349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235153753/10000000000 : ℝ)|^4675 ≤ (33282563484517/100000000000000 : ℝ)^3651
        have hw : |(4235153753/10000000000 : ℝ)|=(4235153753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(896716333/2000000000 : ℝ)|^4675 ≤ (35802717143891/100000000000000 : ℝ)^3651
        have hw : |(896716333/2000000000 : ℝ)|=(896716333/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3997957661/10000000000 : ℝ)|^4675 ≤ (30914719359349/100000000000000 : ℝ)^3651
        have hw : |(3997957661/10000000000 : ℝ)|=(3997957661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1589_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3941/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5461/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2231/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15511/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3941/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5461/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3941/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5461/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3941/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5461/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3941/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5461/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3941/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5461/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3941/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5461/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5461/50000 : ℝ) ^ (4673/1024 : ℝ) ≤ (2043075928445217/50000000000000000000 : ℝ) := by
    have hpowers : (5461/50000 : ℝ)^4673 ≤ (2043075928445217/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5461 : ℕ)^4673*50000000000000000000^1024 ≤ 2043075928445217^1024*50000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5461 50000 2043075928445217 50000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5461/50000 : ℝ)) (X := (2043075928445217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3941/25000 : ℝ) ^ (4673/1024 : ℝ) ≤ (4361135057420459/20000000000000000000 : ℝ) := by
    have hpowers : (3941/25000 : ℝ)^4673 ≤ (4361135057420459/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3941 : ℕ)^4673*20000000000000000000^1024 ≤ 4361135057420459^1024*25000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3941 25000 4361135057420459 20000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3941/25000 : ℝ)) (X := (4361135057420459/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002043075928445217/25000000000000000000 : ℝ) ≤ (312505596091911/312500000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (25002043075928445217/25000000000000000000 : ℝ)^1024 ≤ (312505596091911/312500000000000 : ℝ)^4673 := by
      have hnat : (25002043075928445217 : ℕ)^1024*312500000000000^4673 ≤ 312505596091911^4673*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002043075928445217 25000000000000000000 312505596091911 312500000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312505596091911/312500000000000 : ℝ)) (X := (25002043075928445217/25000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100025891827143992729/100000000000000000000 : ℝ) ≤ (250014182832853/250000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (100025891827143992729/100000000000000000000 : ℝ)^1024 ≤ (250014182832853/250000000000000 : ℝ)^4673 := by
      have hnat : (100025891827143992729 : ℕ)^1024*250000000000000^4673 ≤ 250014182832853^4673*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100025891827143992729 100000000000000000000 250014182832853 250000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250014182832853/250000000000000 : ℝ)) (X := (100025891827143992729/100000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004361135057420459/10000000000000000000 : ℝ) ≤ (625059721980443/625000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (10004361135057420459/10000000000000000000 : ℝ)^1024 ≤ (625059721980443/625000000000000 : ℝ)^4673 := by
      have hnat : (10004361135057420459 : ℕ)^1024*625000000000000^4673 ≤ 625059721980443^4673*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004361135057420459 10000000000000000000 625059721980443 625000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625059721980443/625000000000000 : ℝ)) (X := (10004361135057420459/10000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2043075928445217/50000000000000000000 : ℝ) ≤ ((1512887075057685781/1513125000000000000 : ℝ)+2*(48529796621/60525000000000 : ℝ)*(5461/50000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (1512887075057685781/1513125000000000000 : ℝ)+2*(48529796621/60525000000000 : ℝ)*(5461/50000 : ℝ)=(312505596091911/312500000000000 : ℝ) by norm_num, show 1+2*(2043075928445217/50000000000000000000 : ℝ)=(25002043075928445217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4361135057420459/20000000000000000000 : ℝ)+(2043075928445217/50000000000000000000 : ℝ) ≤ ((1512887075057685781/1513125000000000000 : ℝ)+(48529796621/60525000000000 : ℝ)*((3941/25000 : ℝ)+(5461/50000 : ℝ)))^(4673/1024 : ℝ) := by
    rw [show (1512887075057685781/1513125000000000000 : ℝ)+(48529796621/60525000000000 : ℝ)*((3941/25000 : ℝ)+(5461/50000 : ℝ))=(250014182832853/250000000000000 : ℝ) by norm_num, show 1+(4361135057420459/20000000000000000000 : ℝ)+(2043075928445217/50000000000000000000 : ℝ)=(100025891827143992729/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4361135057420459/20000000000000000000 : ℝ) ≤ ((1512887075057685781/1513125000000000000 : ℝ)+2*(48529796621/60525000000000 : ℝ)*(3941/25000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (1512887075057685781/1513125000000000000 : ℝ)+2*(48529796621/60525000000000 : ℝ)*(3941/25000 : ℝ)=(625059721980443/625000000000000 : ℝ) by norm_num, show 1+2*(4361135057420459/20000000000000000000 : ℝ)=(10004361135057420459/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1512887075057685781/1513125000000000000 : ℝ)*(X 1 0+X 2 0)+(48529796621/60525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (5461/50000 : ℝ)) (hi := (3941/25000 : ℝ)) (c := (1512887075057685781/1513125000000000000 : ℝ)) (alpha := (48529796621/60525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1512887075057685781/1513125000000000000 : ℝ)*(X 0 1+X 2 1)+(48529796621/60525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (5461/50000 : ℝ)) (hi := (3941/25000 : ℝ)) (c := (1512887075057685781/1513125000000000000 : ℝ)) (alpha := (48529796621/60525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1512887075057685781/1513125000000000000 : ℝ)*(X 0 2+X 1 2)+(48529796621/60525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (5461/50000 : ℝ)) (hi := (3941/25000 : ℝ)) (c := (1512887075057685781/1513125000000000000 : ℝ)) (alpha := (48529796621/60525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87989133/500000000 : ℝ)*X 0 0+(5424728747/10000000000 : ℝ)*X 0 1+(652431879/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347364391/10000000000 : ℝ)*X 1 0+(-466197933/2500000000 : ℝ)*X 1 1+(41755641/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347364277/10000000000 : ℝ)*X 2 0+(521945517/1000000000 : ℝ)*X 2 1+(-1864791827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4235088001/10000000000 : ℝ)*X 0 0+(1997670317/5000000000 : ℝ)*X 0 1+(89723603/200000000 : ℝ)*X 0 2+(4235088001/10000000000 : ℝ)*X 1 0+(1997670317/5000000000 : ℝ)*X 1 1+(89723603/200000000 : ℝ)*X 1 2+(4235088001/10000000000 : ℝ)*X 2 0+(1997670317/5000000000 : ℝ)*X 2 1+(89723603/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-879904513/5000000000 : ℝ)*X 0 0+(1044108537/2000000000 : ℝ)*X 0 1+(5423633509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264646807/500000000 : ℝ)*X 1 0+(-66424513/400000000 : ℝ)*X 1 1+(5423634781/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5292936447/10000000000 : ℝ)*X 2 0+(5423633311/10000000000 : ℝ)*X 2 1+(-1660614451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4235153753/10000000000 : ℝ)*X 0 0+(896716333/2000000000 : ℝ)*X 0 1+(3997957661/10000000000 : ℝ)*X 0 2+(4235153753/10000000000 : ℝ)*X 1 0+(896716333/2000000000 : ℝ)*X 1 1+(3997957661/10000000000 : ℝ)*X 1 2+(4235153753/10000000000 : ℝ)*X 2 0+(896716333/2000000000 : ℝ)*X 2 1+(3997957661/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (132516855391481319886644193/12609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (829192061/50000000000000 : ℝ)*(base19) + (730877233/50000000000000 : ℝ)*(base23) + (49608823/100000000000000 : ℝ)*(lower2) + (161496567/50000000000000 : ℝ)*(upper3) + (29077771/20000000000000 : ℝ)*(upper5) + (431809337567057/12500000000000 : ℝ)*(major0) + (431809337567057/12500000000000 : ℝ)*(major1) + (431809337567057/12500000000000 : ℝ)*(major2) + (304473401202133/6250000000000 : ℝ)*(sp0) + (1217899497325791/25000000000000 : ℝ)*(sp1) + (4871598185932821/100000000000000 : ℝ)*(sp2) + (127333534955017/6250000000000 : ℝ)*(sp3) + (12614226579/50000000000000 : ℝ)*(sp4) + (12843792303/100000000000000 : ℝ)*(sp7) + (1018674701536287/50000000000000 : ℝ)*(f.failure) + (4871599647687287/100000000000000 : ℝ)*(f.sum) + (20744573913811/12105000000000000000000000000 : ℝ)*base66 + (33583357919731399/4203125000000000000000000000000 : ℝ)*base68 + (2484230120456101/4203125000000000000000000000000 : ℝ)*base69 + (20630120076825149/4203125000000000000000000000000 : ℝ)*base72 + (58288256253271/12105000000000000000000000000 : ℝ)*base74 + (4261681321112351/4203125000000000000000000000000 : ℝ)*base75 + (16325533607295387/2101562500000000000000000000000 : ℝ)*base78 + (42384734134668899/4203125000000000000000000000000 : ℝ)*base80 + (6652923976631/3026250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (19646039/5000000000000000000000 : ℝ)*base90 + (19646039/5000000000000000000000 : ℝ)*base92 + (19646039/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (74022617706272997474797873/6304687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1760911/2500000000000 : ℝ)*(base23) + (142276811/50000000000000 : ℝ)*(lower2) + (69675719/20000000000000 : ℝ)*(upper3) + (2636343/800000000000 : ℝ)*(lower4) + (109111823540063/3125000000000 : ℝ)*(major0) + (109111823540063/3125000000000 : ℝ)*(major1) + (109111823540063/3125000000000 : ℝ)*(major2) + (124613027/800000000000 : ℝ)*(sp0) + (29189283949/100000000000000 : ℝ)*(sp1) + (5615504257/50000000000000 : ℝ)*(sp3) + (196956346910903/4000000000000 : ℝ)*(sp4) + (4923895060117001/100000000000000 : ℝ)*(sp5) + (492392417896451/10000000000000 : ℝ)*(sp6) + (2059220834791693/100000000000000 : ℝ)*(sp7) + (2059232065800207/100000000000000 : ℝ)*(f.failure) + (98478484988019/2000000000000 : ℝ)*(f.sum) + (128391765391979/12105000000000000000000000000 : ℝ)*base65 + (10225894743519389/4203125000000000000000000000000 : ℝ)*base68 + (1411003709715079/262695312500000000000000000000 : ℝ)*base70 + (18893447120580007/2101562500000000000000000000000 : ℝ)*base72 + (3682757070799/3026250000000000000000000000 : ℝ)*base74 + (14368834599800639/4203125000000000000000000000000 : ℝ)*base76 + (41177638278644389/4203125000000000000000000000000 : ℝ)*base78 + (33320444755074361/4203125000000000000000000000000 : ℝ)*base79 + (41090318666371/12105000000000000000000000000 : ℝ)*base82 + (35761721/10000000000000000000000 : ℝ)*base89 + (35761721/10000000000000000000000 : ℝ)*base91 + (35761721/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1589_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3941/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5461/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15511/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1589_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1589_s4_0 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-879981763/5000000000 : ℝ)*x 0 + (5423512101/10000000000 : ℝ)*x 1 + (5220551511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (879981763/5000000000 : ℝ)^4675 ≤ (1081158204239/10000000000000 : ℝ)^3651 := by
    have hnat : (879981763 : ℕ)^4675*10000000000000^3651 ≤ 1081158204239^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879981763 5000000000 1081158204239 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423512101/10000000000 : ℝ)^4675 ≤ (45682935581553/100000000000000 : ℝ)^3651 := by
    have hnat : (5423512101 : ℕ)^4675*100000000000000^3651 ≤ 45682935581553^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423512101 10000000000 45682935581553 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220551511/10000000000 : ℝ)^4675 ≤ (21752741184743/50000000000000 : ℝ)^3651 := by
    have hnat : (5220551511 : ℕ)^4675*50000000000000^3651 ≤ 21752741184743^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220551511 10000000000 21752741184743 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-879981763/5000000000 : ℝ), (5423512101/10000000000 : ℝ), (5220551511/10000000000 : ℝ)] ![(1081158204239/10000000000000 : ℝ), (45682935581553/100000000000000 : ℝ), (21752741184743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-879981763/5000000000 : ℝ)|^4675 ≤ (1081158204239/10000000000000 : ℝ)^3651
        have hw : |(-879981763/5000000000 : ℝ)|=(879981763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423512101/10000000000 : ℝ)|^4675 ≤ (45682935581553/100000000000000 : ℝ)^3651
        have hw : |(5423512101/10000000000 : ℝ)|=(5423512101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220551511/10000000000 : ℝ)|^4675 ≤ (21752741184743/50000000000000 : ℝ)^3651
        have hw : |(5220551511/10000000000 : ℝ)|=(5220551511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s4_1 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069408181/2000000000 : ℝ)*x 0 + (-1863763213/10000000000 : ℝ)*x 1 + (5220551347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069408181/2000000000 : ℝ)^4675 ≤ (44859786417647/100000000000000 : ℝ)^3651 := by
    have hnat : (1069408181 : ℕ)^4675*100000000000000^3651 ≤ 44859786417647^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069408181 2000000000 44859786417647 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863763213/10000000000 : ℝ)^4675 ≤ (11634732953137/100000000000000 : ℝ)^3651 := by
    have hnat : (1863763213 : ℕ)^4675*100000000000000^3651 ≤ 11634732953137^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863763213 10000000000 11634732953137 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220551347/10000000000 : ℝ)^4675 ≤ (43505480619473/100000000000000 : ℝ)^3651 := by
    have hnat : (5220551347 : ℕ)^4675*100000000000000^3651 ≤ 43505480619473^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220551347 10000000000 43505480619473 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069408181/2000000000 : ℝ), (-1863763213/10000000000 : ℝ), (5220551347/10000000000 : ℝ)] ![(44859786417647/100000000000000 : ℝ), (11634732953137/100000000000000 : ℝ), (43505480619473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069408181/2000000000 : ℝ)|^4675 ≤ (44859786417647/100000000000000 : ℝ)^3651
        have hw : |(1069408181/2000000000 : ℝ)|=(1069408181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1863763213/10000000000 : ℝ)|^4675 ≤ (11634732953137/100000000000000 : ℝ)^3651
        have hw : |(-1863763213/10000000000 : ℝ)|=(1863763213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220551347/10000000000 : ℝ)|^4675 ≤ (43505480619473/100000000000000 : ℝ)^3651
        have hw : |(5220551347/10000000000 : ℝ)|=(5220551347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s4_2 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347040867/10000000000 : ℝ)*x 0 + (326284459/625000000 : ℝ)*x 1 + (-931881633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347040867/10000000000 : ℝ)^4675 ≤ (2803736625589/6250000000000 : ℝ)^3651 := by
    have hnat : (5347040867 : ℕ)^4675*6250000000000^3651 ≤ 2803736625589^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347040867 10000000000 2803736625589 6250000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (326284459/625000000 : ℝ)^4675 ≤ (43505480587461/100000000000000 : ℝ)^3651 := by
    have hnat : (326284459 : ℕ)^4675*100000000000000^3651 ≤ 43505480587461^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326284459 625000000 43505480587461 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931881633/5000000000 : ℝ)^4675 ≤ (11634733376791/100000000000000 : ℝ)^3651 := by
    have hnat : (931881633 : ℕ)^4675*100000000000000^3651 ≤ 11634733376791^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931881633 5000000000 11634733376791 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347040867/10000000000 : ℝ), (326284459/625000000 : ℝ), (-931881633/5000000000 : ℝ)] ![(2803736625589/6250000000000 : ℝ), (43505480587461/100000000000000 : ℝ), (11634733376791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347040867/10000000000 : ℝ)|^4675 ≤ (2803736625589/6250000000000 : ℝ)^3651
        have hw : |(5347040867/10000000000 : ℝ)|=(5347040867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(326284459/625000000 : ℝ)|^4675 ≤ (43505480587461/100000000000000 : ℝ)^3651
        have hw : |(326284459/625000000 : ℝ)|=(326284459/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-931881633/5000000000 : ℝ)|^4675 ≤ (11634733376791/100000000000000 : ℝ)^3651
        have hw : |(-931881633/5000000000 : ℝ)|=(931881633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s4_3 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235202339/10000000000 : ℝ)*x 0 + (3998093167/10000000000 : ℝ)*x 1 + (4483402629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235202339/10000000000 : ℝ)^4675 ≤ (1040095387339/3125000000000 : ℝ)^3651 := by
    have hnat : (4235202339 : ℕ)^4675*3125000000000^3651 ≤ 1040095387339^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235202339 10000000000 1040095387339 3125000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3998093167/10000000000 : ℝ)^4675 ≤ (1932253816609/6250000000000 : ℝ)^3651 := by
    have hnat : (3998093167 : ℕ)^4675*6250000000000^3651 ≤ 1932253816609^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3998093167 10000000000 1932253816609 6250000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483402629/10000000000 : ℝ)^4675 ≤ (17900443261067/50000000000000 : ℝ)^3651 := by
    have hnat : (4483402629 : ℕ)^4675*50000000000000^3651 ≤ 17900443261067^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483402629 10000000000 17900443261067 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235202339/10000000000 : ℝ), (3998093167/10000000000 : ℝ), (4483402629/10000000000 : ℝ)] ![(1040095387339/3125000000000 : ℝ), (1932253816609/6250000000000 : ℝ), (17900443261067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235202339/10000000000 : ℝ)|^4675 ≤ (1040095387339/3125000000000 : ℝ)^3651
        have hw : |(4235202339/10000000000 : ℝ)|=(4235202339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3998093167/10000000000 : ℝ)|^4675 ≤ (1932253816609/6250000000000 : ℝ)^3651
        have hw : |(3998093167/10000000000 : ℝ)|=(3998093167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483402629/10000000000 : ℝ)|^4675 ≤ (17900443261067/50000000000000 : ℝ)^3651
        have hw : |(4483402629/10000000000 : ℝ)|=(4483402629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s4_4 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1759990329/10000000000 : ℝ)*x 0 + (81587713/156250000 : ℝ)*x 1 + (5422441673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1759990329/10000000000 : ℝ)^4675 ≤ (1351474109491/12500000000000 : ℝ)^3651 := by
    have hnat : (1759990329 : ℕ)^4675*12500000000000^3651 ≤ 1351474109491^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759990329 10000000000 1351474109491 12500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81587713/156250000 : ℝ)^4675 ≤ (43516816384171/100000000000000 : ℝ)^3651 := by
    have hnat : (81587713 : ℕ)^4675*100000000000000^3651 ≤ 43516816384171^3651*156250000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81587713 156250000 43516816384171 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422441673/10000000000 : ℝ)^4675 ≤ (45671390723109/100000000000000 : ℝ)^3651 := by
    have hnat : (5422441673 : ℕ)^4675*100000000000000^3651 ≤ 45671390723109^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422441673 10000000000 45671390723109 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1759990329/10000000000 : ℝ), (81587713/156250000 : ℝ), (5422441673/10000000000 : ℝ)] ![(1351474109491/12500000000000 : ℝ), (43516816384171/100000000000000 : ℝ), (45671390723109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1759990329/10000000000 : ℝ)|^4675 ≤ (1351474109491/12500000000000 : ℝ)^3651
        have hw : |(-1759990329/10000000000 : ℝ)|=(1759990329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81587713/156250000 : ℝ)|^4675 ≤ (43516816384171/100000000000000 : ℝ)^3651
        have hw : |(81587713/156250000 : ℝ)|=(81587713/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422441673/10000000000 : ℝ)|^4675 ≤ (45671390723109/100000000000000 : ℝ)^3651
        have hw : |(5422441673/10000000000 : ℝ)|=(5422441673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s4_5 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293227793/10000000000 : ℝ)*x 0 + (-1661872661/10000000000 : ℝ)*x 1 + (5422441029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293227793/10000000000 : ℝ)^4675 ≤ (8856501226633/20000000000000 : ℝ)^3651 := by
    have hnat : (5293227793 : ℕ)^4675*20000000000000^3651 ≤ 8856501226633^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293227793 10000000000 8856501226633 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1661872661/10000000000 : ℝ)^4675 ≤ (5023055035353/50000000000000 : ℝ)^3651 := by
    have hnat : (1661872661 : ℕ)^4675*50000000000000^3651 ≤ 5023055035353^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661872661 10000000000 5023055035353 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422441029/10000000000 : ℝ)^4675 ≤ (9134276755517/20000000000000 : ℝ)^3651 := by
    have hnat : (5422441029 : ℕ)^4675*20000000000000^3651 ≤ 9134276755517^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422441029 10000000000 9134276755517 20000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293227793/10000000000 : ℝ), (-1661872661/10000000000 : ℝ), (5422441029/10000000000 : ℝ)] ![(8856501226633/20000000000000 : ℝ), (5023055035353/50000000000000 : ℝ), (9134276755517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293227793/10000000000 : ℝ)|^4675 ≤ (8856501226633/20000000000000 : ℝ)^3651
        have hw : |(5293227793/10000000000 : ℝ)|=(5293227793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1661872661/10000000000 : ℝ)|^4675 ≤ (5023055035353/50000000000000 : ℝ)^3651
        have hw : |(-1661872661/10000000000 : ℝ)|=(1661872661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422441029/10000000000 : ℝ)|^4675 ≤ (9134276755517/20000000000000 : ℝ)^3651
        have hw : |(5422441029/10000000000 : ℝ)|=(5422441029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s4_6 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293226901/10000000000 : ℝ)*x 0 + (1355610439/2500000000 : ℝ)*x 1 + (-1661872883/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293226901/10000000000 : ℝ)^4675 ≤ (44282496577823/100000000000000 : ℝ)^3651 := by
    have hnat : (5293226901 : ℕ)^4675*100000000000000^3651 ≤ 44282496577823^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293226901 10000000000 44282496577823 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355610439/2500000000 : ℝ)^4675 ≤ (22835695809131/50000000000000 : ℝ)^3651 := by
    have hnat : (1355610439 : ℕ)^4675*50000000000000^3651 ≤ 22835695809131^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355610439 2500000000 22835695809131 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1661872883/10000000000 : ℝ)^4675 ≤ (10046111789101/100000000000000 : ℝ)^3651 := by
    have hnat : (1661872883 : ℕ)^4675*100000000000000^3651 ≤ 10046111789101^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661872883 10000000000 10046111789101 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293226901/10000000000 : ℝ), (1355610439/2500000000 : ℝ), (-1661872883/10000000000 : ℝ)] ![(44282496577823/100000000000000 : ℝ), (22835695809131/50000000000000 : ℝ), (10046111789101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293226901/10000000000 : ℝ)|^4675 ≤ (44282496577823/100000000000000 : ℝ)^3651
        have hw : |(5293226901/10000000000 : ℝ)|=(5293226901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355610439/2500000000 : ℝ)|^4675 ≤ (22835695809131/50000000000000 : ℝ)^3651
        have hw : |(1355610439/2500000000 : ℝ)|=(1355610439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1661872883/10000000000 : ℝ)|^4675 ≤ (10046111789101/100000000000000 : ℝ)^3651
        have hw : |(-1661872883/10000000000 : ℝ)|=(1661872883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s4_7 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (847053021/2000000000 : ℝ)*x 0 + (224043089/500000000 : ℝ)*x 1 + (2000326379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847053021/2000000000 : ℝ)^4675 ≤ (16641841998879/50000000000000 : ℝ)^3651 := by
    have hnat : (847053021 : ℕ)^4675*50000000000000^3651 ≤ 16641841998879^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847053021 2000000000 16641841998879 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (224043089/500000000 : ℝ)^4675 ≤ (17887454427257/50000000000000 : ℝ)^3651 := by
    have hnat : (224043089 : ℕ)^4675*50000000000000^3651 ≤ 17887454427257^3651*500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224043089 500000000 17887454427257 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2000326379/5000000000 : ℝ)^4675 ≤ (30941407133169/100000000000000 : ℝ)^3651 := by
    have hnat : (2000326379 : ℕ)^4675*100000000000000^3651 ≤ 30941407133169^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2000326379 5000000000 30941407133169 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(847053021/2000000000 : ℝ), (224043089/500000000 : ℝ), (2000326379/5000000000 : ℝ)] ![(16641841998879/50000000000000 : ℝ), (17887454427257/50000000000000 : ℝ), (30941407133169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(847053021/2000000000 : ℝ)|^4675 ≤ (16641841998879/50000000000000 : ℝ)^3651
        have hw : |(847053021/2000000000 : ℝ)|=(847053021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(224043089/500000000 : ℝ)|^4675 ≤ (17887454427257/50000000000000 : ℝ)^3651
        have hw : |(224043089/500000000 : ℝ)|=(224043089/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2000326379/5000000000 : ℝ)|^4675 ≤ (30941407133169/100000000000000 : ℝ)^3651
        have hw : |(2000326379/5000000000 : ℝ)|=(2000326379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1589_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11179/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7743/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2231/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2231/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2231/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2231/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2231/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2231/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2231/20000 : ℝ) ^ (4673/1024 : ℝ) ≤ (899869898243617/20000000000000000000 : ℝ) := by
    have hpowers : (2231/20000 : ℝ)^4673 ≤ (899869898243617/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2231 : ℕ)^4673*20000000000000000000^1024 ≤ 899869898243617^1024*20000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2231 20000 899869898243617 20000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2231/20000 : ℝ)) (X := (899869898243617/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15511/100000 : ℝ) ^ (4673/1024 : ℝ) ≤ (5063417001603791/25000000000000000000 : ℝ) := by
    have hpowers : (15511/100000 : ℝ)^4673 ≤ (5063417001603791/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15511 : ℕ)^4673*25000000000000000000^1024 ≤ 5063417001603791^1024*100000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15511 100000 5063417001603791 25000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15511/100000 : ℝ)) (X := (5063417001603791/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000899869898243617/10000000000000000000 : ℝ) ≤ (10000197182624161/10000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (10000899869898243617/10000000000000000000 : ℝ)^1024 ≤ (10000197182624161/10000000000000000 : ℝ)^4673 := by
      have hnat : (10000899869898243617 : ℕ)^1024*10000000000000000^4673 ≤ 10000197182624161^4673*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000899869898243617 10000000000000000000 10000197182624161 10000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000197182624161/10000000000000000 : ℝ)) (X := (10000899869898243617/10000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024753017497633249/100000000000000000000 : ℝ) ≤ (10000542363377397/10000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (100024753017497633249/100000000000000000000 : ℝ)^1024 ≤ (10000542363377397/10000000000000000 : ℝ)^4673 := by
      have hnat : (100024753017497633249 : ℕ)^1024*10000000000000000^4673 ≤ 10000542363377397^4673*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024753017497633249 100000000000000000000 10000542363377397 10000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000542363377397/10000000000000000 : ℝ)) (X := (100024753017497633249/100000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505063417001603791/12500000000000000000 : ℝ) ≤ (10000887544130633/10000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (12505063417001603791/12500000000000000000 : ℝ)^1024 ≤ (10000887544130633/10000000000000000 : ℝ)^4673 := by
      have hnat : (12505063417001603791 : ℕ)^1024*10000000000000000^4673 ≤ 10000887544130633^4673*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505063417001603791 12500000000000000000 10000887544130633 10000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000887544130633/10000000000000000 : ℝ)) (X := (12505063417001603791/12500000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(899869898243617/20000000000000000000 : ℝ) ≤ ((989844498747867049/990000000000000000 : ℝ)+2*(7845017119/9900000000000 : ℝ)*(2231/20000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (989844498747867049/990000000000000000 : ℝ)+2*(7845017119/9900000000000 : ℝ)*(2231/20000 : ℝ)=(10000197182624161/10000000000000000 : ℝ) by norm_num, show 1+2*(899869898243617/20000000000000000000 : ℝ)=(10000899869898243617/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5063417001603791/25000000000000000000 : ℝ)+(899869898243617/20000000000000000000 : ℝ) ≤ ((989844498747867049/990000000000000000 : ℝ)+(7845017119/9900000000000 : ℝ)*((15511/100000 : ℝ)+(2231/20000 : ℝ)))^(4673/1024 : ℝ) := by
    rw [show (989844498747867049/990000000000000000 : ℝ)+(7845017119/9900000000000 : ℝ)*((15511/100000 : ℝ)+(2231/20000 : ℝ))=(10000542363377397/10000000000000000 : ℝ) by norm_num, show 1+(5063417001603791/25000000000000000000 : ℝ)+(899869898243617/20000000000000000000 : ℝ)=(100024753017497633249/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5063417001603791/25000000000000000000 : ℝ) ≤ ((989844498747867049/990000000000000000 : ℝ)+2*(7845017119/9900000000000 : ℝ)*(15511/100000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (989844498747867049/990000000000000000 : ℝ)+2*(7845017119/9900000000000 : ℝ)*(15511/100000 : ℝ)=(10000887544130633/10000000000000000 : ℝ) by norm_num, show 1+2*(5063417001603791/25000000000000000000 : ℝ)=(12505063417001603791/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (989844498747867049/990000000000000000 : ℝ)*(X 1 0+X 2 0)+(7845017119/9900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (15511/100000 : ℝ)) (c := (989844498747867049/990000000000000000 : ℝ)) (alpha := (7845017119/9900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (989844498747867049/990000000000000000 : ℝ)*(X 0 1+X 2 1)+(7845017119/9900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (15511/100000 : ℝ)) (c := (989844498747867049/990000000000000000 : ℝ)) (alpha := (7845017119/9900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (989844498747867049/990000000000000000 : ℝ)*(X 0 2+X 1 2)+(7845017119/9900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (2231/20000 : ℝ)) (hi := (15511/100000 : ℝ)) (c := (989844498747867049/990000000000000000 : ℝ)) (alpha := (7845017119/9900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-879981763/5000000000 : ℝ)*X 0 0+(5423512101/10000000000 : ℝ)*X 0 1+(5220551511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069408181/2000000000 : ℝ)*X 1 0+(-1863763213/10000000000 : ℝ)*X 1 1+(5220551347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347040867/10000000000 : ℝ)*X 2 0+(326284459/625000000 : ℝ)*X 2 1+(-931881633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4235202339/10000000000 : ℝ)*X 0 0+(3998093167/10000000000 : ℝ)*X 0 1+(4483402629/10000000000 : ℝ)*X 0 2+(4235202339/10000000000 : ℝ)*X 1 0+(3998093167/10000000000 : ℝ)*X 1 1+(4483402629/10000000000 : ℝ)*X 1 2+(4235202339/10000000000 : ℝ)*X 2 0+(3998093167/10000000000 : ℝ)*X 2 1+(4483402629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1759990329/10000000000 : ℝ)*X 0 0+(81587713/156250000 : ℝ)*X 0 1+(5422441673/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5293227793/10000000000 : ℝ)*X 1 0+(-1661872661/10000000000 : ℝ)*X 1 1+(5422441029/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293226901/10000000000 : ℝ)*X 2 0+(1355610439/2500000000 : ℝ)*X 2 1+(-1661872883/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((847053021/2000000000 : ℝ)*X 0 0+(224043089/500000000 : ℝ)*X 0 1+(2000326379/5000000000 : ℝ)*X 0 2+(847053021/2000000000 : ℝ)*X 1 0+(224043089/500000000 : ℝ)*X 1 1+(2000326379/5000000000 : ℝ)*X 1 2+(847053021/2000000000 : ℝ)*X 2 0+(224043089/500000000 : ℝ)*X 2 1+(2000326379/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8624373432231582368422301/1650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (395767483/50000000000000 : ℝ)*(base19) + (127035377/20000000000000 : ℝ)*(base23) + (12976479/20000000000000 : ℝ)*(lower2) + (6270907/4000000000000 : ℝ)*(upper3) + (1217563/12500000000000 : ℝ)*(upper5) + (698763512268149/20000000000000 : ℝ)*(major0) + (698763512268149/20000000000000 : ℝ)*(major1) + (698763512268149/20000000000000 : ℝ)*(major2) + (246353764581521/5000000000000 : ℝ)*(sp0) + (4927081470878367/100000000000000 : ℝ)*(sp1) + (153971300851139/3125000000000 : ℝ)*(sp2) + (2060545815889347/100000000000000 : ℝ)*(sp3) + (6970782913/100000000000000 : ℝ)*(sp4) + (6870149039/100000000000000 : ℝ)*(sp7) + (1030276343019193/50000000000000 : ℝ)*(f.failure) + (4927082262413333/100000000000000 : ℝ)*(f.sum) + (55993621469/49500000000000000000000000 : ℝ)*base66 + (134594513176577699/19800000000000000000000000000000 : ℝ)*base68 + (182039017538777699/19800000000000000000000000000000 : ℝ)*base70 + (32691141324977699/19800000000000000000000000000000 : ℝ)*base72 + (212688131129/99000000000000000000000000 : ℝ)*base73 + (72008680682777699/19800000000000000000000000000000 : ℝ)*base76 + (94057643288777699/19800000000000000000000000000000 : ℝ)*base78 + (172523214038622301/19800000000000000000000000000000 : ℝ)*base79 + (1882083583/1546875000000000000000000 : ℝ)*base82 + (7683521/5000000000000000000000 : ℝ)*base90 + (7683521/5000000000000000000000 : ℝ)*base92 + (7683521/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15421637857456404682477187/1500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321832283/10000000000000 : ℝ)*(base19) + (670766077/25000000000000 : ℝ)*(base23) + (22602119/12500000000000 : ℝ)*(upper2) + (6497933/2000000000000 : ℝ)*(upper3) + (7430361/2000000000000 : ℝ)*(upper5) + (3530900192438407/100000000000000 : ℝ)*(major0) + (3530900192438407/100000000000000 : ℝ)*(major1) + (3530900192438407/100000000000000 : ℝ)*(major2) + (4099455263/10000000000000 : ℝ)*(sp1) + (37280872827/100000000000000 : ℝ)*(sp2) + (497937709136849/10000000000000 : ℝ)*(sp4) + (497933287849303/10000000000000 : ℝ)*(sp5) + (1244834281857839/25000000000000 : ℝ)*(sp6) + (416484590161051/20000000000000 : ℝ)*(sp7) + (416484590161051/20000000000000 : ℝ)*(f.failure) + (497937709136849/10000000000000 : ℝ)*(f.sum) + (604622362621/247500000000000000000000000 : ℝ)*base66 + (934967309919349057/99000000000000000000000000000000 : ℝ)*base68 + (357277959560650943/99000000000000000000000000000000 : ℝ)*base69 + (542060206715650943/99000000000000000000000000000000 : ℝ)*base71 + (3364181346167/495000000000000000000000000 : ℝ)*base74 + (258640625270650943/99000000000000000000000000000000 : ℝ)*base75 + (336150559959349057/99000000000000000000000000000000 : ℝ)*base78 + (711721970624650943/99000000000000000000000000000000 : ℝ)*base79 + (1208926635767/495000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (3205453/2000000000000000000000 : ℝ)*base89 + (3205453/2000000000000000000000 : ℝ)*base91 + (3205453/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1589_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2231/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1589_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1589_s5_0 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1759979541/10000000000 : ℝ)*x 0 + (2711698547/5000000000 : ℝ)*x 1 + (1305163987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1759979541/10000000000 : ℝ)^4675 ≤ (10811708016953/100000000000000 : ℝ)^3651 := by
    have hnat : (1759979541 : ℕ)^4675*100000000000000^3651 ≤ 10811708016953^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759979541 10000000000 10811708016953 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711698547/5000000000 : ℝ)^4675 ≤ (4568169516899/10000000000000 : ℝ)^3651 := by
    have hnat : (2711698547 : ℕ)^4675*10000000000000^3651 ≤ 4568169516899^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711698547 5000000000 4568169516899 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1305163987/2500000000 : ℝ)^4675 ≤ (5438324599999/12500000000000 : ℝ)^3651 := by
    have hnat : (1305163987 : ℕ)^4675*12500000000000^3651 ≤ 5438324599999^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305163987 2500000000 5438324599999 12500000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1759979541/10000000000 : ℝ), (2711698547/5000000000 : ℝ), (1305163987/2500000000 : ℝ)] ![(10811708016953/100000000000000 : ℝ), (4568169516899/10000000000000 : ℝ), (5438324599999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1759979541/10000000000 : ℝ)|^4675 ≤ (10811708016953/100000000000000 : ℝ)^3651
        have hw : |(-1759979541/10000000000 : ℝ)|=(1759979541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711698547/5000000000 : ℝ)|^4675 ≤ (4568169516899/10000000000000 : ℝ)^3651
        have hw : |(2711698547/5000000000 : ℝ)|=(2711698547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1305163987/2500000000 : ℝ)|^4675 ≤ (5438324599999/12500000000000 : ℝ)^3651
        have hw : |(1305163987/2500000000 : ℝ)|=(1305163987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s5_1 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673505401/5000000000 : ℝ)*x 0 + (-465916037/2500000000 : ℝ)*x 1 + (5220655861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673505401/5000000000 : ℝ)^4675 ≤ (22429731515191/50000000000000 : ℝ)^3651 := by
    have hnat : (2673505401 : ℕ)^4675*50000000000000^3651 ≤ 22429731515191^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673505401 5000000000 22429731515191 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (465916037/2500000000 : ℝ)^4675 ≤ (11633941085721/100000000000000 : ℝ)^3651 := by
    have hnat : (465916037 : ℕ)^4675*100000000000000^3651 ≤ 11633941085721^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465916037 2500000000 11633941085721 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220655861/10000000000 : ℝ)^4675 ≤ (21753297935813/50000000000000 : ℝ)^3651 := by
    have hnat : (5220655861 : ℕ)^4675*50000000000000^3651 ≤ 21753297935813^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220655861 10000000000 21753297935813 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673505401/5000000000 : ℝ), (-465916037/2500000000 : ℝ), (5220655861/10000000000 : ℝ)] ![(22429731515191/50000000000000 : ℝ), (11633941085721/100000000000000 : ℝ), (21753297935813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673505401/5000000000 : ℝ)|^4675 ≤ (22429731515191/50000000000000 : ℝ)^3651
        have hw : |(2673505401/5000000000 : ℝ)|=(2673505401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-465916037/2500000000 : ℝ)|^4675 ≤ (11633941085721/100000000000000 : ℝ)^3651
        have hw : |(-465916037/2500000000 : ℝ)|=(465916037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220655861/10000000000 : ℝ)|^4675 ≤ (21753297935813/50000000000000 : ℝ)^3651
        have hw : |(5220655861/10000000000 : ℝ)|=(5220655861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s5_2 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069402159/2000000000 : ℝ)*x 0 + (1044131157/2000000000 : ℝ)*x 1 + (-931832129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069402159/2000000000 : ℝ)^4675 ≤ (44859462955183/100000000000000 : ℝ)^3651 := by
    have hnat : (1069402159 : ℕ)^4675*100000000000000^3651 ≤ 44859462955183^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069402159 2000000000 44859462955183 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044131157/2000000000 : ℝ)^4675 ≤ (271916219129/625000000000 : ℝ)^3651 := by
    have hnat : (1044131157 : ℕ)^4675*625000000000^3651 ≤ 271916219129^3651*2000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044131157 2000000000 271916219129 625000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931832129/5000000000 : ℝ)^4675 ≤ (1163394196499/10000000000000 : ℝ)^3651 := by
    have hnat : (931832129 : ℕ)^4675*10000000000000^3651 ≤ 1163394196499^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931832129 5000000000 1163394196499 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069402159/2000000000 : ℝ), (1044131157/2000000000 : ℝ), (-931832129/5000000000 : ℝ)] ![(44859462955183/100000000000000 : ℝ), (271916219129/625000000000 : ℝ), (1163394196499/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069402159/2000000000 : ℝ)|^4675 ≤ (44859462955183/100000000000000 : ℝ)^3651
        have hw : |(1069402159/2000000000 : ℝ)|=(1069402159/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044131157/2000000000 : ℝ)|^4675 ≤ (271916219129/625000000000 : ℝ)^3651
        have hw : |(1044131157/2000000000 : ℝ)|=(1044131157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-931832129/5000000000 : ℝ)|^4675 ≤ (1163394196499/10000000000000 : ℝ)^3651
        have hw : |(-931832129/5000000000 : ℝ)|=(931832129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s5_3 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235213083/10000000000 : ℝ)*x 0 + (249897177/625000000 : ℝ)*x 1 + (224156933/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235213083/10000000000 : ℝ)^4675 ≤ (33283160509591/100000000000000 : ℝ)^3651 := by
    have hnat : (4235213083 : ℕ)^4675*100000000000000^3651 ≤ 33283160509591^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235213083 10000000000 33283160509591 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249897177/625000000 : ℝ)^4675 ≤ (30918651965739/100000000000000 : ℝ)^3651 := by
    have hnat : (249897177 : ℕ)^4675*100000000000000^3651 ≤ 30918651965739^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249897177 625000000 30918651965739 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224156933/500000000 : ℝ)^4675 ≤ (17899093753989/50000000000000 : ℝ)^3651 := by
    have hnat : (224156933 : ℕ)^4675*50000000000000^3651 ≤ 17899093753989^3651*500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224156933 500000000 17899093753989 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235213083/10000000000 : ℝ), (249897177/625000000 : ℝ), (224156933/500000000 : ℝ)] ![(33283160509591/100000000000000 : ℝ), (30918651965739/100000000000000 : ℝ), (17899093753989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235213083/10000000000 : ℝ)|^4675 ≤ (33283160509591/100000000000000 : ℝ)^3651
        have hw : |(4235213083/10000000000 : ℝ)|=(4235213083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249897177/625000000 : ℝ)|^4675 ≤ (30918651965739/100000000000000 : ℝ)^3651
        have hw : |(249897177/625000000 : ℝ)|=(249897177/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224156933/500000000 : ℝ)|^4675 ≤ (17899093753989/50000000000000 : ℝ)^3651
        have hw : |(224156933/500000000 : ℝ)|=(224156933/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s5_4 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1760005619/10000000000 : ℝ)*x 0 + (1305429089/2500000000 : ℝ)*x 1 + (5422328879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1760005619/10000000000 : ℝ)^4675 ≤ (5405956574061/50000000000000 : ℝ)^3651 := by
    have hnat : (1760005619 : ℕ)^4675*50000000000000^3651 ≤ 5405956574061^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1760005619 10000000000 5405956574061 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1305429089/2500000000 : ℝ)^4675 ≤ (2175895629901/5000000000000 : ℝ)^3651 := by
    have hnat : (1305429089 : ℕ)^4675*5000000000000^3651 ≤ 2175895629901^3651*2500000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1305429089 2500000000 2175895629901 5000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422328879/10000000000 : ℝ)^4675 ≤ (1826806969849/4000000000000 : ℝ)^3651 := by
    have hnat : (5422328879 : ℕ)^4675*4000000000000^3651 ≤ 1826806969849^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422328879 10000000000 1826806969849 4000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1760005619/10000000000 : ℝ), (1305429089/2500000000 : ℝ), (5422328879/10000000000 : ℝ)] ![(5405956574061/50000000000000 : ℝ), (2175895629901/5000000000000 : ℝ), (1826806969849/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1760005619/10000000000 : ℝ)|^4675 ≤ (5405956574061/50000000000000 : ℝ)^3651
        have hw : |(-1760005619/10000000000 : ℝ)|=(1760005619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1305429089/2500000000 : ℝ)|^4675 ≤ (2175895629901/5000000000000 : ℝ)^3651
        have hw : |(1305429089/2500000000 : ℝ)|=(1305429089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422328879/10000000000 : ℝ)|^4675 ≤ (1826806969849/4000000000000 : ℝ)^3651
        have hw : |(5422328879/10000000000 : ℝ)|=(5422328879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s5_5 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646627541/5000000000 : ℝ)*x 0 + (-1661990797/10000000000 : ℝ)*x 1 + (338895571/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646627541/5000000000 : ℝ)^4675 ≤ (44282798460431/100000000000000 : ℝ)^3651 := by
    have hnat : (2646627541 : ℕ)^4675*100000000000000^3651 ≤ 44282798460431^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646627541 5000000000 44282798460431 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1661990797/10000000000 : ℝ)^4675 ≤ (10047024513543/100000000000000 : ℝ)^3651 := by
    have hnat : (1661990797 : ℕ)^4675*100000000000000^3651 ≤ 10047024513543^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661990797 10000000000 10047024513543 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338895571/625000000 : ℝ)^4675 ≤ (45670177017947/100000000000000 : ℝ)^3651 := by
    have hnat : (338895571 : ℕ)^4675*100000000000000^3651 ≤ 45670177017947^3651*625000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338895571 625000000 45670177017947 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646627541/5000000000 : ℝ), (-1661990797/10000000000 : ℝ), (338895571/625000000 : ℝ)] ![(44282798460431/100000000000000 : ℝ), (10047024513543/100000000000000 : ℝ), (45670177017947/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646627541/5000000000 : ℝ)|^4675 ≤ (44282798460431/100000000000000 : ℝ)^3651
        have hw : |(2646627541/5000000000 : ℝ)|=(2646627541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1661990797/10000000000 : ℝ)|^4675 ≤ (10047024513543/100000000000000 : ℝ)^3651
        have hw : |(-1661990797/10000000000 : ℝ)|=(1661990797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338895571/625000000 : ℝ)|^4675 ≤ (45670177017947/100000000000000 : ℝ)^3651
        have hw : |(338895571/625000000 : ℝ)|=(338895571/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s5_6 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646627589/5000000000 : ℝ)*x 0 + (84723889/156250000 : ℝ)*x 1 + (-1661990997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646627589/5000000000 : ℝ)^4675 ≤ (4428279948881/10000000000000 : ℝ)^3651 := by
    have hnat : (2646627589 : ℕ)^4675*10000000000000^3651 ≤ 4428279948881^3651*5000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646627589 5000000000 4428279948881 10000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84723889/156250000 : ℝ)^4675 ≤ (356798237731/781250000000 : ℝ)^3651 := by
    have hnat : (84723889 : ℕ)^4675*781250000000^3651 ≤ 356798237731^3651*156250000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84723889 156250000 356798237731 781250000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1661990997/10000000000 : ℝ)^4675 ≤ (10047026061677/100000000000000 : ℝ)^3651 := by
    have hnat : (1661990997 : ℕ)^4675*100000000000000^3651 ≤ 10047026061677^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1661990997 10000000000 10047026061677 100000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646627589/5000000000 : ℝ), (84723889/156250000 : ℝ), (-1661990997/10000000000 : ℝ)] ![(4428279948881/10000000000000 : ℝ), (356798237731/781250000000 : ℝ), (10047026061677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646627589/5000000000 : ℝ)|^4675 ≤ (4428279948881/10000000000000 : ℝ)^3651
        have hw : |(2646627589/5000000000 : ℝ)|=(2646627589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84723889/156250000 : ℝ)|^4675 ≤ (356798237731/781250000000 : ℝ)^3651
        have hw : |(84723889/156250000 : ℝ)|=(84723889/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1661990997/10000000000 : ℝ)|^4675 ≤ (10047026061677/100000000000000 : ℝ)^3651
        have hw : |(-1661990997/10000000000 : ℝ)|=(1661990997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1589_s5_7 (p : ℝ) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4235275161/10000000000 : ℝ)*x 0 + (4480603287/10000000000 : ℝ)*x 1 + (4000909379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4235275161/10000000000 : ℝ)^4675 ≤ (2080236574357/6250000000000 : ℝ)^3651 := by
    have hnat : (4235275161 : ℕ)^4675*6250000000000^3651 ≤ 2080236574357^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235275161 10000000000 2080236574357 6250000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4480603287/10000000000 : ℝ)^4675 ≤ (17886133125391/50000000000000 : ℝ)^3651 := by
    have hnat : (4480603287 : ℕ)^4675*50000000000000^3651 ≤ 17886133125391^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480603287 10000000000 17886133125391 50000000000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4000909379/10000000000 : ℝ)^4675 ≤ (483499196019/1562500000000 : ℝ)^3651 := by
    have hnat : (4000909379 : ℕ)^4675*1562500000000^3651 ≤ 483499196019^3651*10000000000^4675 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4000909379 10000000000 483499196019 1562500000000 4675 3651 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4675/1024 : ℝ)) 4675 3651 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4235275161/10000000000 : ℝ), (4480603287/10000000000 : ℝ), (4000909379/10000000000 : ℝ)] ![(2080236574357/6250000000000 : ℝ), (17886133125391/50000000000000 : ℝ), (483499196019/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4235275161/10000000000 : ℝ)|^4675 ≤ (2080236574357/6250000000000 : ℝ)^3651
        have hw : |(4235275161/10000000000 : ℝ)|=(4235275161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4480603287/10000000000 : ℝ)|^4675 ≤ (17886133125391/50000000000000 : ℝ)^3651
        have hw : |(4480603287/10000000000 : ℝ)|=(4480603287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4000909379/10000000000 : ℝ)|^4675 ≤ (483499196019/1562500000000 : ℝ)^3651
        have hw : |(4000909379/10000000000 : ℝ)|=(4000909379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1589_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11181/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11179/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11179/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11179/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11179/100000 : ℝ) ^ (4673/1024 : ℝ) ≤ (567961904061537/12500000000000000000 : ℝ) := by
    have hpowers : (11179/100000 : ℝ)^4673 ≤ (567961904061537/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11179 : ℕ)^4673*12500000000000000000^1024 ≤ 567961904061537^1024*100000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11179 100000 567961904061537 12500000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11179/100000 : ℝ)) (X := (567961904061537/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7743/50000 : ℝ) ^ (4673/1024 : ℝ) ≤ (10052562455216167/50000000000000000000 : ℝ) := by
    have hpowers : (7743/50000 : ℝ)^4673 ≤ (10052562455216167/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7743 : ℕ)^4673*50000000000000000000^1024 ≤ 10052562455216167^1024*50000^4673 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7743 50000 10052562455216167 50000000000000000000 4673 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7743/50000 : ℝ)) (X := (10052562455216167/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250567961904061537/6250000000000000000 : ℝ) ≤ (10000199125993847/10000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (6250567961904061537/6250000000000000000 : ℝ)^1024 ≤ (10000199125993847/10000000000000000 : ℝ)^4673 := by
      have hnat : (6250567961904061537 : ℕ)^1024*10000000000000000^4673 ≤ 10000199125993847^4673*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250567961904061537 6250000000000000000 10000199125993847 10000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000199125993847/10000000000000000 : ℝ)) (X := (6250567961904061537/6250000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002464882014292463/10000000000000000000 : ℝ) ≤ (5000270040264393/5000000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (10002464882014292463/10000000000000000000 : ℝ)^1024 ≤ (5000270040264393/5000000000000000 : ℝ)^4673 := by
      have hnat : (10002464882014292463 : ℕ)^1024*5000000000000000^4673 ≤ 5000270040264393^4673*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002464882014292463 10000000000000000000 5000270040264393 5000000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000270040264393/5000000000000000 : ℝ)) (X := (10002464882014292463/10000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010052562455216167/25000000000000000000 : ℝ) ≤ (400035241402549/400000000000000 : ℝ) ^ (4673/1024 : ℝ) := by
    have hpowers : (25010052562455216167/25000000000000000000 : ℝ)^1024 ≤ (400035241402549/400000000000000 : ℝ)^4673 := by
      have hnat : (25010052562455216167 : ℕ)^1024*400000000000000^4673 ≤ 400035241402549^4673*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010052562455216167 25000000000000000000 400035241402549 400000000000000 1024 4673 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400035241402549/400000000000000 : ℝ)) (X := (25010052562455216167/25000000000000000000 : ℝ)) (by norm_num) 4673 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(567961904061537/12500000000000000000 : ℝ) ≤ ((43063234574163332867/43070000000000000000 : ℝ)+2*(340954534939/430700000000000 : ℝ)*(11179/100000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (43063234574163332867/43070000000000000000 : ℝ)+2*(340954534939/430700000000000 : ℝ)*(11179/100000 : ℝ)=(10000199125993847/10000000000000000 : ℝ) by norm_num, show 1+2*(567961904061537/12500000000000000000 : ℝ)=(6250567961904061537/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10052562455216167/50000000000000000000 : ℝ)+(567961904061537/12500000000000000000 : ℝ) ≤ ((43063234574163332867/43070000000000000000 : ℝ)+(340954534939/430700000000000 : ℝ)*((7743/50000 : ℝ)+(11179/100000 : ℝ)))^(4673/1024 : ℝ) := by
    rw [show (43063234574163332867/43070000000000000000 : ℝ)+(340954534939/430700000000000 : ℝ)*((7743/50000 : ℝ)+(11179/100000 : ℝ))=(5000270040264393/5000000000000000 : ℝ) by norm_num, show 1+(10052562455216167/50000000000000000000 : ℝ)+(567961904061537/12500000000000000000 : ℝ)=(10002464882014292463/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10052562455216167/50000000000000000000 : ℝ) ≤ ((43063234574163332867/43070000000000000000 : ℝ)+2*(340954534939/430700000000000 : ℝ)*(7743/50000 : ℝ))^(4673/1024 : ℝ) := by
    rw [show (43063234574163332867/43070000000000000000 : ℝ)+2*(340954534939/430700000000000 : ℝ)*(7743/50000 : ℝ)=(400035241402549/400000000000000 : ℝ) by norm_num, show 1+2*(10052562455216167/50000000000000000000 : ℝ)=(25010052562455216167/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43063234574163332867/43070000000000000000 : ℝ)*(X 1 0+X 2 0)+(340954534939/430700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (43063234574163332867/43070000000000000000 : ℝ)) (alpha := (340954534939/430700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43063234574163332867/43070000000000000000 : ℝ)*(X 0 1+X 2 1)+(340954534939/430700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (43063234574163332867/43070000000000000000 : ℝ)) (alpha := (340954534939/430700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43063234574163332867/43070000000000000000 : ℝ)*(X 0 2+X 1 2)+(340954534939/430700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4673/1024 : ℝ)) (lo := (11179/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (43063234574163332867/43070000000000000000 : ℝ)) (alpha := (340954534939/430700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1759979541/10000000000 : ℝ)*X 0 0+(2711698547/5000000000 : ℝ)*X 0 1+(1305163987/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673505401/5000000000 : ℝ)*X 1 0+(-465916037/2500000000 : ℝ)*X 1 1+(5220655861/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069402159/2000000000 : ℝ)*X 2 0+(1044131157/2000000000 : ℝ)*X 2 1+(-931832129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4235213083/10000000000 : ℝ)*X 0 0+(249897177/625000000 : ℝ)*X 0 1+(224156933/500000000 : ℝ)*X 0 2+(4235213083/10000000000 : ℝ)*X 1 0+(249897177/625000000 : ℝ)*X 1 1+(224156933/500000000 : ℝ)*X 1 2+(4235213083/10000000000 : ℝ)*X 2 0+(249897177/625000000 : ℝ)*X 2 1+(224156933/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1760005619/10000000000 : ℝ)*X 0 0+(1305429089/2500000000 : ℝ)*X 0 1+(5422328879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646627541/5000000000 : ℝ)*X 1 0+(-1661990797/10000000000 : ℝ)*X 1 1+(338895571/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646627589/5000000000 : ℝ)*X 2 0+(84723889/156250000 : ℝ)*X 2 1+(-1661990997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4235275161/10000000000 : ℝ)*X 0 0+(4480603287/10000000000 : ℝ)*X 0 1+(4000909379/10000000000 : ℝ)*X 0 2+(4235275161/10000000000 : ℝ)*X 1 0+(4480603287/10000000000 : ℝ)*X 1 1+(4000909379/10000000000 : ℝ)*X 1 2+(4235275161/10000000000 : ℝ)*X 2 0+(4480603287/10000000000 : ℝ)*X 2 1+(4000909379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1589_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14584523966864701817508319209/2153500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (725559947/50000000000000 : ℝ)*(base19) + (1383253667/100000000000000 : ℝ)*(base23) + (23523101/10000000000000 : ℝ)*(upper3) + (8208859/25000000000000 : ℝ)*(upper4) + (79349013/100000000000000 : ℝ)*(upper5) + (3497618996849397/100000000000000 : ℝ)*(major0) + (3497618996849397/100000000000000 : ℝ)*(major1) + (3497618996849397/100000000000000 : ℝ)*(major2) + (2466211253746321/50000000000000 : ℝ)*(sp0) + (4932441653924893/100000000000000 : ℝ)*(sp1) + (61655521522389/1250000000000 : ℝ)*(sp2) + (412556779533343/20000000000000 : ℝ)*(sp3) + (4119510429/20000000000000 : ℝ)*(sp4) + (1076523813/10000000000000 : ℝ)*(sp7) + (412558932580969/20000000000000 : ℝ)*(f.failure) + (4932443105044787/100000000000000 : ℝ)*(f.sum) + (49717710482853/21535000000000000000000000000 : ℝ)*base65 + (65756678419651531199/4307000000000000000000000000000000 : ℝ)*base67 + (34715969703170531199/4307000000000000000000000000000000 : ℝ)*base69 + (29516291321630531199/4307000000000000000000000000000000 : ℝ)*base71 + (34954761031873/21535000000000000000000000000 : ℝ)*base73 + (44497951429956531199/4307000000000000000000000000000000 : ℝ)*base75 + (43266620477932531199/4307000000000000000000000000000000 : ℝ)*base77 + (90603489079427531199/4307000000000000000000000000000000 : ℝ)*base79 + (131265724630567/21535000000000000000000000000 : ℝ)*base82 + (7233393/2000000000000000000000 : ℝ)*base90 + (7233393/2000000000000000000000 : ℝ)*base92 + (7233393/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3191909332884691814168858919/538375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (570260191/50000000000000 : ℝ)*(base19) + (1394781933/100000000000000 : ℝ)*(base23) + (529118539/100000000000000 : ℝ)*(lower1) + (6036497/6250000000000 : ℝ)*(upper2) + (16825453/20000000000000 : ℝ)*(upper3) + (4104267/5000000000000 : ℝ)*(upper5) + (883669626329827/25000000000000 : ℝ)*(major0) + (883669626329827/25000000000000 : ℝ)*(major1) + (883669626329827/25000000000000 : ℝ)*(major2) + (916180373/50000000000000 : ℝ)*(sp1) + (2492352761199371/50000000000000 : ℝ)*(sp4) + (2492351274758807/50000000000000 : ℝ)*(sp5) + (623088015952101/12500000000000 : ℝ)*(sp6) + (416930258122743/20000000000000 : ℝ)*(sp7) + (416930258122743/20000000000000 : ℝ)*(f.failure) + (2492352761199371/50000000000000 : ℝ)*(f.sum) + (46017293326883/21535000000000000000000000000 : ℝ)*base66 + (688256356737074009/1076750000000000000000000000000000 : ℝ)*base67 + (10271226001056574009/1076750000000000000000000000000000 : ℝ)*base69 + (6260415643190574009/1076750000000000000000000000000000 : ℝ)*base71 + (58706719331653/21535000000000000000000000000 : ℝ)*base74 + (463364803370574009/1076750000000000000000000000000000 : ℝ)*base75 + (14046352701818574009/1076750000000000000000000000000000 : ℝ)*base77 + (17724099749859074009/1076750000000000000000000000000000 : ℝ)*base79 + (174915578069397/21535000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (13957871/2000000000000000000000 : ℝ)*base90 + (13957871/2000000000000000000000 : ℝ)*base92 + (13957871/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1589_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1589_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1589_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3941/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5461/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1589_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1589_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1589_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4673/1024 : ℝ) ≤ p) (hpb : p ≤ (4675/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (169557303/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3941/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5461/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11181/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1589_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
