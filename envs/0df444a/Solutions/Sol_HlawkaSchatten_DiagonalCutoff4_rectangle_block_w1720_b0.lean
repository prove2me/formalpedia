-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1720_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:58:35.378468+00:00
-- url     : https://prove2.me/submissions/91a0e1aa-7f6f-4216-8050-606691fbd64c

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
theorem support_rectangle_w1720_s0_0 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1307662799/10000000000 : ℝ)*x 0 + (2839146367/5000000000 : ℝ)*x 1 + (4970492927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1307662799/10000000000 : ℝ)^5383 ≤ (405430352497/5000000000000 : ℝ)^4359 := by
    have hnat : (1307662799 : ℕ)^5383*5000000000000^4359 ≤ 405430352497^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307662799 10000000000 405430352497 5000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2839146367/5000000000 : ℝ)^5383 ≤ (49714094828381/100000000000000 : ℝ)^4359 := by
    have hnat : (2839146367 : ℕ)^5383*100000000000000^4359 ≤ 49714094828381^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2839146367 5000000000 49714094828381 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4970492927/10000000000 : ℝ)^5383 ≤ (42177298103469/100000000000000 : ℝ)^4359 := by
    have hnat : (4970492927 : ℕ)^5383*100000000000000^4359 ≤ 42177298103469^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4970492927 10000000000 42177298103469 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1307662799/10000000000 : ℝ), (2839146367/5000000000 : ℝ), (4970492927/10000000000 : ℝ)] ![(405430352497/5000000000000 : ℝ), (49714094828381/100000000000000 : ℝ), (42177298103469/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1307662799/10000000000 : ℝ)|^5383 ≤ (405430352497/5000000000000 : ℝ)^4359
        have hw : |(-1307662799/10000000000 : ℝ)|=(1307662799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2839146367/5000000000 : ℝ)|^5383 ≤ (49714094828381/100000000000000 : ℝ)^4359
        have hw : |(2839146367/5000000000 : ℝ)|=(2839146367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4970492927/10000000000 : ℝ)|^5383 ≤ (42177298103469/100000000000000 : ℝ)^4359
        have hw : |(4970492927/10000000000 : ℝ)|=(4970492927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s0_1 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5397377629/10000000000 : ℝ)*x 0 + (-84485849/500000000 : ℝ)*x 1 + (4970492349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5397377629/10000000000 : ℝ)^5383 ≤ (5836845561811/12500000000000 : ℝ)^4359 := by
    have hnat : (5397377629 : ℕ)^5383*12500000000000^4359 ≤ 5836845561811^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397377629 10000000000 5836845561811 12500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84485849/500000000 : ℝ)^5383 ≤ (5563971721693/50000000000000 : ℝ)^4359 := by
    have hnat : (84485849 : ℕ)^5383*50000000000000^4359 ≤ 5563971721693^4359*500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84485849 500000000 5563971721693 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4970492349/10000000000 : ℝ)^5383 ≤ (843545840933/2000000000000 : ℝ)^4359 := by
    have hnat : (4970492349 : ℕ)^5383*2000000000000^4359 ≤ 843545840933^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4970492349 10000000000 843545840933 2000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5397377629/10000000000 : ℝ), (-84485849/500000000 : ℝ), (4970492349/10000000000 : ℝ)] ![(5836845561811/12500000000000 : ℝ), (5563971721693/50000000000000 : ℝ), (843545840933/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5397377629/10000000000 : ℝ)|^5383 ≤ (5836845561811/12500000000000 : ℝ)^4359
        have hw : |(5397377629/10000000000 : ℝ)|=(5397377629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-84485849/500000000 : ℝ)|^5383 ≤ (5563971721693/50000000000000 : ℝ)^4359
        have hw : |(-84485849/500000000 : ℝ)|=(84485849/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4970492349/10000000000 : ℝ)|^5383 ≤ (843545840933/2000000000000 : ℝ)^4359
        have hw : |(4970492349/10000000000 : ℝ)|=(4970492349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s0_2 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079475321/2000000000 : ℝ)*x 0 + (497049293/1000000000 : ℝ)*x 1 + (-1689717577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079475321/2000000000 : ℝ)^5383 ≤ (11673688388587/25000000000000 : ℝ)^4359 := by
    have hnat : (1079475321 : ℕ)^5383*25000000000000^4359 ≤ 11673688388587^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079475321 2000000000 11673688388587 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497049293/1000000000 : ℝ)^5383 ≤ (21088649067453/50000000000000 : ℝ)^4359 := by
    have hnat : (497049293 : ℕ)^5383*50000000000000^4359 ≤ 21088649067453^4359*1000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497049293 1000000000 21088649067453 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1689717577/10000000000 : ℝ)^5383 ≤ (222558965973/2000000000000 : ℝ)^4359 := by
    have hnat : (1689717577 : ℕ)^5383*2000000000000^4359 ≤ 222558965973^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1689717577 10000000000 222558965973 2000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079475321/2000000000 : ℝ), (497049293/1000000000 : ℝ), (-1689717577/10000000000 : ℝ)] ![(11673688388587/25000000000000 : ℝ), (21088649067453/50000000000000 : ℝ), (222558965973/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079475321/2000000000 : ℝ)|^5383 ≤ (11673688388587/25000000000000 : ℝ)^4359
        have hw : |(1079475321/2000000000 : ℝ)|=(1079475321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(497049293/1000000000 : ℝ)|^5383 ≤ (21088649067453/50000000000000 : ℝ)^4359
        have hw : |(497049293/1000000000 : ℝ)|=(497049293/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1689717577/10000000000 : ℝ)|^5383 ≤ (222558965973/2000000000000 : ℝ)^4359
        have hw : |(-1689717577/10000000000 : ℝ)|=(1689717577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s0_3 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2015628213/5000000000 : ℝ)*x 0 + (3065270631/10000000000 : ℝ)*x 1 + (5164219709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2015628213/5000000000 : ℝ)^5383 ≤ (32565065972527/100000000000000 : ℝ)^4359 := by
    have hnat : (2015628213 : ℕ)^5383*100000000000000^4359 ≤ 32565065972527^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015628213 5000000000 32565065972527 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3065270631/10000000000 : ℝ)^5383 ≤ (11609192233069/50000000000000 : ℝ)^4359 := by
    have hnat : (3065270631 : ℕ)^5383*50000000000000^4359 ≤ 11609192233069^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3065270631 10000000000 11609192233069 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5164219709/10000000000 : ℝ)^5383 ≤ (44216549557207/100000000000000 : ℝ)^4359 := by
    have hnat : (5164219709 : ℕ)^5383*100000000000000^4359 ≤ 44216549557207^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5164219709 10000000000 44216549557207 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2015628213/5000000000 : ℝ), (3065270631/10000000000 : ℝ), (5164219709/10000000000 : ℝ)] ![(32565065972527/100000000000000 : ℝ), (11609192233069/50000000000000 : ℝ), (44216549557207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2015628213/5000000000 : ℝ)|^5383 ≤ (32565065972527/100000000000000 : ℝ)^4359
        have hw : |(2015628213/5000000000 : ℝ)|=(2015628213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3065270631/10000000000 : ℝ)|^5383 ≤ (11609192233069/50000000000000 : ℝ)^4359
        have hw : |(3065270631/10000000000 : ℝ)|=(3065270631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5164219709/10000000000 : ℝ)|^5383 ≤ (44216549557207/100000000000000 : ℝ)^4359
        have hw : |(5164219709/10000000000 : ℝ)|=(5164219709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s0_4 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-52367311/400000000 : ℝ)*x 0 + (19950783/40000000 : ℝ)*x 1 + (283026481/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (52367311/400000000 : ℝ)^5383 ≤ (8120247881341/100000000000000 : ℝ)^4359 := by
    have hnat : (52367311 : ℕ)^5383*100000000000000^4359 ≤ 8120247881341^4359*400000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52367311 400000000 8120247881341 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19950783/40000000 : ℝ)^5383 ≤ (42357638443971/100000000000000 : ℝ)^4359 := by
    have hnat : (19950783 : ℕ)^5383*100000000000000^4359 ≤ 42357638443971^4359*40000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19950783 40000000 42357638443971 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283026481/500000000 : ℝ)^5383 ≤ (12380528414063/25000000000000 : ℝ)^4359 := by
    have hnat : (283026481 : ℕ)^5383*25000000000000^4359 ≤ 12380528414063^4359*500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283026481 500000000 12380528414063 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-52367311/400000000 : ℝ), (19950783/40000000 : ℝ), (283026481/500000000 : ℝ)] ![(8120247881341/100000000000000 : ℝ), (42357638443971/100000000000000 : ℝ), (12380528414063/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-52367311/400000000 : ℝ)|^5383 ≤ (8120247881341/100000000000000 : ℝ)^4359
        have hw : |(-52367311/400000000 : ℝ)|=(52367311/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(19950783/40000000 : ℝ)|^5383 ≤ (42357638443971/100000000000000 : ℝ)^4359
        have hw : |(19950783/40000000 : ℝ)|=(19950783/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283026481/500000000 : ℝ)|^5383 ≤ (12380528414063/25000000000000 : ℝ)^4359
        have hw : |(283026481/500000000 : ℝ)|=(283026481/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s0_5 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1041186541/2000000000 : ℝ)*x 0 + (-199936273/2000000000 : ℝ)*x 1 + (5660530009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1041186541/2000000000 : ℝ)^5383 ≤ (44658018369179/100000000000000 : ℝ)^4359 := by
    have hnat : (1041186541 : ℕ)^5383*100000000000000^4359 ≤ 44658018369179^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041186541 2000000000 44658018369179 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199936273/2000000000 : ℝ)^5383 ≤ (5819863759213/100000000000000 : ℝ)^4359 := by
    have hnat : (199936273 : ℕ)^5383*100000000000000^4359 ≤ 5819863759213^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199936273 2000000000 5819863759213 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660530009/10000000000 : ℝ)^5383 ≤ (619026473237/1250000000000 : ℝ)^4359 := by
    have hnat : (5660530009 : ℕ)^5383*1250000000000^4359 ≤ 619026473237^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660530009 10000000000 619026473237 1250000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1041186541/2000000000 : ℝ), (-199936273/2000000000 : ℝ), (5660530009/10000000000 : ℝ)] ![(44658018369179/100000000000000 : ℝ), (5819863759213/100000000000000 : ℝ), (619026473237/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1041186541/2000000000 : ℝ)|^5383 ≤ (44658018369179/100000000000000 : ℝ)^4359
        have hw : |(1041186541/2000000000 : ℝ)|=(1041186541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199936273/2000000000 : ℝ)|^5383 ≤ (5819863759213/100000000000000 : ℝ)^4359
        have hw : |(-199936273/2000000000 : ℝ)|=(199936273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660530009/10000000000 : ℝ)|^5383 ≤ (619026473237/1250000000000 : ℝ)^4359
        have hw : |(5660530009/10000000000 : ℝ)|=(5660530009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s0_6 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5205933891/10000000000 : ℝ)*x 0 + (1132105811/2000000000 : ℝ)*x 1 + (-19993621/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5205933891/10000000000 : ℝ)^5383 ≤ (44658030933039/100000000000000 : ℝ)^4359 := by
    have hnat : (5205933891 : ℕ)^5383*100000000000000^4359 ≤ 44658030933039^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205933891 10000000000 44658030933039 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132105811/2000000000 : ℝ)^5383 ≤ (24761053776031/50000000000000 : ℝ)^4359 := by
    have hnat : (1132105811 : ℕ)^5383*50000000000000^4359 ≤ 24761053776031^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132105811 2000000000 24761053776031 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19993621/200000000 : ℝ)^5383 ≤ (5819861494573/100000000000000 : ℝ)^4359 := by
    have hnat : (19993621 : ℕ)^5383*100000000000000^4359 ≤ 5819861494573^4359*200000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19993621 200000000 5819861494573 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5205933891/10000000000 : ℝ), (1132105811/2000000000 : ℝ), (-19993621/200000000 : ℝ)] ![(44658030933039/100000000000000 : ℝ), (24761053776031/50000000000000 : ℝ), (5819861494573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5205933891/10000000000 : ℝ)|^5383 ≤ (44658030933039/100000000000000 : ℝ)^4359
        have hw : |(5205933891/10000000000 : ℝ)|=(5205933891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132105811/2000000000 : ℝ)|^5383 ≤ (24761053776031/50000000000000 : ℝ)^4359
        have hw : |(1132105811/2000000000 : ℝ)|=(1132105811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19993621/200000000 : ℝ)|^5383 ≤ (5819861494573/100000000000000 : ℝ)^4359
        have hw : |(-19993621/200000000 : ℝ)|=(19993621/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s0_7 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4035768047/10000000000 : ℝ)*x 0 + (5113206239/10000000000 : ℝ)*x 1 + (3117949153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4035768047/10000000000 : ℝ)^5383 ≤ (8152519763077/25000000000000 : ℝ)^4359 := by
    have hnat : (4035768047 : ℕ)^5383*25000000000000^4359 ≤ 8152519763077^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035768047 10000000000 8152519763077 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5113206239/10000000000 : ℝ)^5383 ≤ (4367778745063/10000000000000 : ℝ)^4359 := by
    have hnat : (5113206239 : ℕ)^5383*10000000000000^4359 ≤ 4367778745063^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5113206239 10000000000 4367778745063 10000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3117949153/10000000000 : ℝ)^5383 ≤ (5928033369363/25000000000000 : ℝ)^4359 := by
    have hnat : (3117949153 : ℕ)^5383*25000000000000^4359 ≤ 5928033369363^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117949153 10000000000 5928033369363 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4035768047/10000000000 : ℝ), (5113206239/10000000000 : ℝ), (3117949153/10000000000 : ℝ)] ![(8152519763077/25000000000000 : ℝ), (4367778745063/10000000000000 : ℝ), (5928033369363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4035768047/10000000000 : ℝ)|^5383 ≤ (8152519763077/25000000000000 : ℝ)^4359
        have hw : |(4035768047/10000000000 : ℝ)|=(4035768047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5113206239/10000000000 : ℝ)|^5383 ≤ (4367778745063/10000000000000 : ℝ)^4359
        have hw : |(5113206239/10000000000 : ℝ)|=(5113206239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3117949153/10000000000 : ℝ)|^5383 ≤ (5928033369363/25000000000000 : ℝ)^4359
        have hw : |(3117949153/10000000000 : ℝ)|=(3117949153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1720_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (6333/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4313/20000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (5375/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5375 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5375*1^1024 ≤ 0^1024*1^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5375/1024 : ℝ) ≤ (815086251578373523/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5375 ≤ (815086251578373523/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5375*100000000000000000000^1024 ≤ 815086251578373523^1024*5^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 815086251578373523 100000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (815086251578373523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5375 := by
      have hnat : (1 : ℕ)^1024*1^5375 ≤ 1^5375*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100815086251578373523/100000000000000000000 : ℝ) ≤ (10015477363070213/10000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (100815086251578373523/100000000000000000000 : ℝ)^1024 ≤ (10015477363070213/10000000000000000 : ℝ)^5375 := by
      have hnat : (100815086251578373523 : ℕ)^1024*10000000000000000^5375 ≤ 10015477363070213^5375*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100815086251578373523 100000000000000000000 10015477363070213 10000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015477363070213/10000000000000000 : ℝ)) (X := (100815086251578373523/100000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50815086251578373523/50000000000000000000 : ℝ) ≤ (5015477363070213/5000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (50815086251578373523/50000000000000000000 : ℝ)^1024 ≤ (5015477363070213/5000000000000000 : ℝ)^5375 := by
      have hnat : (50815086251578373523 : ℕ)^1024*5000000000000000^5375 ≤ 5015477363070213^5375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50815086251578373523 50000000000000000000 5015477363070213 5000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015477363070213/5000000000000000 : ℝ)) (X := (50815086251578373523/50000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15477363070213/4000000000000000 : ℝ)*(0 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15477363070213/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(815086251578373523/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15477363070213/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5375/1024 : ℝ) := by
    rw [show (1 : ℝ)+(15477363070213/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10015477363070213/10000000000000000 : ℝ) by norm_num, show 1+(815086251578373523/100000000000000000000 : ℝ)+(0 : ℝ)=(100815086251578373523/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(815086251578373523/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15477363070213/4000000000000000 : ℝ)*(2/5 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15477363070213/4000000000000000 : ℝ)*(2/5 : ℝ)=(5015477363070213/5000000000000000 : ℝ) by norm_num, show 1+2*(815086251578373523/100000000000000000000 : ℝ)=(50815086251578373523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15477363070213/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15477363070213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15477363070213/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15477363070213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15477363070213/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (15477363070213/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1307662799/10000000000 : ℝ)*X 0 0+(2839146367/5000000000 : ℝ)*X 0 1+(4970492927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5397377629/10000000000 : ℝ)*X 1 0+(-84485849/500000000 : ℝ)*X 1 1+(4970492349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1079475321/2000000000 : ℝ)*X 2 0+(497049293/1000000000 : ℝ)*X 2 1+(-1689717577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2015628213/5000000000 : ℝ)*X 0 0+(3065270631/10000000000 : ℝ)*X 0 1+(5164219709/10000000000 : ℝ)*X 0 2+(2015628213/5000000000 : ℝ)*X 1 0+(3065270631/10000000000 : ℝ)*X 1 1+(5164219709/10000000000 : ℝ)*X 1 2+(2015628213/5000000000 : ℝ)*X 2 0+(3065270631/10000000000 : ℝ)*X 2 1+(5164219709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-52367311/400000000 : ℝ)*X 0 0+(19950783/40000000 : ℝ)*X 0 1+(283026481/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1041186541/2000000000 : ℝ)*X 1 0+(-199936273/2000000000 : ℝ)*X 1 1+(5660530009/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5205933891/10000000000 : ℝ)*X 2 0+(1132105811/2000000000 : ℝ)*X 2 1+(-19993621/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4035768047/10000000000 : ℝ)*X 0 0+(5113206239/10000000000 : ℝ)*X 0 1+(3117949153/10000000000 : ℝ)*X 0 2+(4035768047/10000000000 : ℝ)*X 1 0+(5113206239/10000000000 : ℝ)*X 1 1+(3117949153/10000000000 : ℝ)*X 1 2+(4035768047/10000000000 : ℝ)*X 2 0+(5113206239/10000000000 : ℝ)*X 2 1+(3117949153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (246241772148531816623589/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3600493/2000000000000 : ℝ)*(base1) + (40344331/3125000000000 : ℝ)*(base19) + (127871617/12500000000000 : ℝ)*(base23) + (80998483/25000000000000 : ℝ)*(upper3) + (160399/800000000000 : ℝ)*(upper5) + (944634087360949/100000000000000 : ℝ)*(major0) + (944634087360949/100000000000000 : ℝ)*(major1) + (944634087360949/100000000000000 : ℝ)*(major2) + (1412834541137613/100000000000000 : ℝ)*(sp0) + (706417652247023/50000000000000 : ℝ)*(sp1) + (706417786269851/50000000000000 : ℝ)*(sp2) + (238214796055131/50000000000000 : ℝ)*(sp3) + (1117199837/50000000000000 : ℝ)*(sp4) + (800936433/50000000000000 : ℝ)*(sp7) + (238215687003889/50000000000000 : ℝ)*(f.failure) + (706418297756319/50000000000000 : ℝ)*(f.sum) + (68676925912137/200000000000000000000000000000 : ℝ)*base65 + (4816267066112137/400000000000000000000000000000 : ℝ)*base67 + (2622696006512137/400000000000000000000000000000 : ℝ)*base69 + (1676372062112137/400000000000000000000000000000 : ℝ)*base71 + (1092228318112137/200000000000000000000000000000 : ℝ)*base73 + (342722762687863/400000000000000000000000000000 : ℝ)*base76 + (1290622151712137/400000000000000000000000000000 : ℝ)*base77 + (363420098912137/400000000000000000000000000000 : ℝ)*base79 + (976834520912137/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (3626619/1000000000000000000000 : ℝ)*base89 + (3626619/1000000000000000000000 : ℝ)*base91 + (3626619/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (188056660012193780382057/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (265018799/100000000000000 : ℝ)*(base19) + (645170103/100000000000000 : ℝ)*(base23) + (299591559/50000000000000 : ℝ)*(base32) + (101668097/50000000000000 : ℝ)*(base37) + (4996571/6250000000000 : ℝ)*(upper3) + (993719361187543/100000000000000 : ℝ)*(major0) + (993719361187543/100000000000000 : ℝ)*(major1) + (124214920148443/12500000000000 : ℝ)*(major2) + (1345928353/100000000000000 : ℝ)*(sp1) + (1238022571/50000000000000 : ℝ)*(sp2) + (743125304167043/50000000000000 : ℝ)*(sp4) + (371562249346733/25000000000000 : ℝ)*(sp5) + (37156187177971/2500000000000 : ℝ)*(sp6) + (501186998093911/100000000000000 : ℝ)*(sp7) + (250593900306611/50000000000000 : ℝ)*(f.failure) + (743125304167043/50000000000000 : ℝ)*(f.sum) + (154327563816469/400000000000000000000000000000 : ℝ)*base66 + (439388069821641/50000000000000000000000000000 : ℝ)*base68 + (1701382288756659/400000000000000000000000000000 : ℝ)*base69 + (94559795928359/50000000000000000000000000000 : ℝ)*base71 + (2637592140616469/400000000000000000000000000000 : ℝ)*base74 + (5941187782756659/400000000000000000000000000000 : ℝ)*base75 + (1618152296843341/400000000000000000000000000000 : ℝ)*base78 + (3293545025643341/400000000000000000000000000000 : ℝ)*base80 + (486016719843341/200000000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (2331119/1000000000000000000000 : ℝ)*base90 + (2331119/1000000000000000000000 : ℝ)*base92 + (12331119/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1720_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6333/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4313/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1720_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1720_s1_0 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-686918579/5000000000 : ℝ)*x 0 + (2737866373/5000000000 : ℝ)*x 1 + (5129371553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (686918579/5000000000 : ℝ)^5383 ≤ (4309156165873/50000000000000 : ℝ)^4359 := by
    have hnat : (686918579 : ℕ)^5383*50000000000000^4359 ≤ 4309156165873^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686918579 5000000000 4309156165873 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737866373/5000000000 : ℝ)^5383 ≤ (2376665579063/5000000000000 : ℝ)^4359 := by
    have hnat : (2737866373 : ℕ)^5383*5000000000000^4359 ≤ 2376665579063^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737866373 5000000000 2376665579063 5000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129371553/10000000000 : ℝ)^5383 ≤ (43848376083261/100000000000000 : ℝ)^4359 := by
    have hnat : (5129371553 : ℕ)^5383*100000000000000^4359 ≤ 43848376083261^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129371553 10000000000 43848376083261 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-686918579/5000000000 : ℝ), (2737866373/5000000000 : ℝ), (5129371553/10000000000 : ℝ)] ![(4309156165873/50000000000000 : ℝ), (2376665579063/5000000000000 : ℝ), (43848376083261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-686918579/5000000000 : ℝ)|^5383 ≤ (4309156165873/50000000000000 : ℝ)^4359
        have hw : |(-686918579/5000000000 : ℝ)|=(686918579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737866373/5000000000 : ℝ)|^5383 ≤ (2376665579063/5000000000000 : ℝ)^4359
        have hw : |(2737866373/5000000000 : ℝ)|=(2737866373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129371553/10000000000 : ℝ)|^5383 ≤ (43848376083261/100000000000000 : ℝ)^4359
        have hw : |(5129371553/10000000000 : ℝ)|=(5129371553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s1_1 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343428721/10000000000 : ℝ)*x 0 + (-1553717121/10000000000 : ℝ)*x 1 + (5129370559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343428721/10000000000 : ℝ)^5383 ≤ (46119067359477/100000000000000 : ℝ)^4359 := by
    have hnat : (5343428721 : ℕ)^5383*100000000000000^4359 ≤ 46119067359477^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343428721 10000000000 46119067359477 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1553717121/10000000000 : ℝ)^5383 ≤ (2006513407253/20000000000000 : ℝ)^4359 := by
    have hnat : (1553717121 : ℕ)^5383*20000000000000^4359 ≤ 2006513407253^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1553717121 10000000000 2006513407253 20000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129370559/10000000000 : ℝ)^5383 ≤ (21924182794967/50000000000000 : ℝ)^4359 := by
    have hnat : (5129370559 : ℕ)^5383*50000000000000^4359 ≤ 21924182794967^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129370559 10000000000 21924182794967 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343428721/10000000000 : ℝ), (-1553717121/10000000000 : ℝ), (5129370559/10000000000 : ℝ)] ![(46119067359477/100000000000000 : ℝ), (2006513407253/20000000000000 : ℝ), (21924182794967/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343428721/10000000000 : ℝ)|^5383 ≤ (46119067359477/100000000000000 : ℝ)^4359
        have hw : |(5343428721/10000000000 : ℝ)|=(5343428721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1553717121/10000000000 : ℝ)|^5383 ≤ (2006513407253/20000000000000 : ℝ)^4359
        have hw : |(-1553717121/10000000000 : ℝ)|=(1553717121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129370559/10000000000 : ℝ)|^5383 ≤ (21924182794967/50000000000000 : ℝ)^4359
        have hw : |(5129370559/10000000000 : ℝ)|=(5129370559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s1_2 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5343427523/10000000000 : ℝ)*x 0 + (1282342859/2500000000 : ℝ)*x 1 + (-776858781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5343427523/10000000000 : ℝ)^5383 ≤ (23059527295269/50000000000000 : ℝ)^4359 := by
    have hnat : (5343427523 : ℕ)^5383*50000000000000^4359 ≤ 23059527295269^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5343427523 10000000000 23059527295269 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282342859/2500000000 : ℝ)^5383 ≤ (43848374848131/100000000000000 : ℝ)^4359 := by
    have hnat : (1282342859 : ℕ)^5383*100000000000000^4359 ≤ 43848374848131^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282342859 2500000000 43848374848131 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (776858781/5000000000 : ℝ)^5383 ≤ (1003257055281/10000000000000 : ℝ)^4359 := by
    have hnat : (776858781 : ℕ)^5383*10000000000000^4359 ≤ 1003257055281^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      776858781 5000000000 1003257055281 10000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5343427523/10000000000 : ℝ), (1282342859/2500000000 : ℝ), (-776858781/5000000000 : ℝ)] ![(23059527295269/50000000000000 : ℝ), (43848374848131/100000000000000 : ℝ), (1003257055281/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5343427523/10000000000 : ℝ)|^5383 ≤ (23059527295269/50000000000000 : ℝ)^4359
        have hw : |(5343427523/10000000000 : ℝ)|=(5343427523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282342859/2500000000 : ℝ)|^5383 ≤ (43848374848131/100000000000000 : ℝ)^4359
        have hw : |(1282342859/2500000000 : ℝ)|=(1282342859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-776858781/5000000000 : ℝ)|^5383 ≤ (1003257055281/10000000000000 : ℝ)^4359
        have hw : |(-776858781/5000000000 : ℝ)|=(776858781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s1_3 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4089817549/10000000000 : ℝ)*x 0 + (449515499/1250000000 : ℝ)*x 1 + (4623239107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4089817549/10000000000 : ℝ)^5383 ≤ (33150254928877/100000000000000 : ℝ)^4359 := by
    have hnat : (4089817549 : ℕ)^5383*100000000000000^4359 ≤ 33150254928877^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4089817549 10000000000 33150254928877 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449515499/1250000000 : ℝ)^5383 ≤ (28280884889887/100000000000000 : ℝ)^4359 := by
    have hnat : (449515499 : ℕ)^5383*100000000000000^4359 ≤ 28280884889887^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449515499 1250000000 28280884889887 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4623239107/10000000000 : ℝ)^5383 ≤ (9642215039667/25000000000000 : ℝ)^4359 := by
    have hnat : (4623239107 : ℕ)^5383*25000000000000^4359 ≤ 9642215039667^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4623239107 10000000000 9642215039667 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4089817549/10000000000 : ℝ), (449515499/1250000000 : ℝ), (4623239107/10000000000 : ℝ)] ![(33150254928877/100000000000000 : ℝ), (28280884889887/100000000000000 : ℝ), (9642215039667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4089817549/10000000000 : ℝ)|^5383 ≤ (33150254928877/100000000000000 : ℝ)^4359
        have hw : |(4089817549/10000000000 : ℝ)|=(4089817549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(449515499/1250000000 : ℝ)|^5383 ≤ (28280884889887/100000000000000 : ℝ)^4359
        have hw : |(449515499/1250000000 : ℝ)|=(449515499/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4623239107/10000000000 : ℝ)|^5383 ≤ (9642215039667/25000000000000 : ℝ)^4359
        have hw : |(4623239107/10000000000 : ℝ)|=(4623239107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s1_4 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-687007883/5000000000 : ℝ)*x 0 + (1283375319/2500000000 : ℝ)*x 1 + (2735768047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (687007883/5000000000 : ℝ)^5383 ≤ (4309848000069/50000000000000 : ℝ)^4359 := by
    have hnat : (687007883 : ℕ)^5383*50000000000000^4359 ≤ 4309848000069^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      687007883 5000000000 4309848000069 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1283375319/2500000000 : ℝ)^5383 ≤ (43891976320051/100000000000000 : ℝ)^4359 := by
    have hnat : (1283375319 : ℕ)^5383*100000000000000^4359 ≤ 43891976320051^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1283375319 2500000000 43891976320051 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2735768047/5000000000 : ℝ)^5383 ≤ (189953310689/400000000000 : ℝ)^4359 := by
    have hnat : (2735768047 : ℕ)^5383*400000000000^4359 ≤ 189953310689^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2735768047 5000000000 189953310689 400000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-687007883/5000000000 : ℝ), (1283375319/2500000000 : ℝ), (2735768047/5000000000 : ℝ)] ![(4309848000069/50000000000000 : ℝ), (43891976320051/100000000000000 : ℝ), (189953310689/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-687007883/5000000000 : ℝ)|^5383 ≤ (4309848000069/50000000000000 : ℝ)^4359
        have hw : |(-687007883/5000000000 : ℝ)|=(687007883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1283375319/2500000000 : ℝ)|^5383 ≤ (43891976320051/100000000000000 : ℝ)^4359
        have hw : |(1283375319/2500000000 : ℝ)|=(1283375319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2735768047/5000000000 : ℝ)|^5383 ≤ (189953310689/400000000000 : ℝ)^4359
        have hw : |(2735768047/5000000000 : ℝ)|=(2735768047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s1_5 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5250683183/10000000000 : ℝ)*x 0 + (-605776207/5000000000 : ℝ)*x 1 + (1367883943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250683183/10000000000 : ℝ)^5383 ≤ (45132559003571/100000000000000 : ℝ)^4359 := by
    have hnat : (5250683183 : ℕ)^5383*100000000000000^4359 ≤ 45132559003571^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250683183 10000000000 45132559003571 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605776207/5000000000 : ℝ)^5383 ≤ (1844779189463/25000000000000 : ℝ)^4359 := by
    have hnat : (605776207 : ℕ)^5383*25000000000000^4359 ≤ 1844779189463^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605776207 5000000000 1844779189463 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367883943/2500000000 : ℝ)^5383 ≤ (47488324221043/100000000000000 : ℝ)^4359 := by
    have hnat : (1367883943 : ℕ)^5383*100000000000000^4359 ≤ 47488324221043^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367883943 2500000000 47488324221043 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250683183/10000000000 : ℝ), (-605776207/5000000000 : ℝ), (1367883943/2500000000 : ℝ)] ![(45132559003571/100000000000000 : ℝ), (1844779189463/25000000000000 : ℝ), (47488324221043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250683183/10000000000 : ℝ)|^5383 ≤ (45132559003571/100000000000000 : ℝ)^4359
        have hw : |(5250683183/10000000000 : ℝ)|=(5250683183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-605776207/5000000000 : ℝ)|^5383 ≤ (1844779189463/25000000000000 : ℝ)^4359
        have hw : |(-605776207/5000000000 : ℝ)|=(605776207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367883943/2500000000 : ℝ)|^5383 ≤ (47488324221043/100000000000000 : ℝ)^4359
        have hw : |(1367883943/2500000000 : ℝ)|=(1367883943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s1_6 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328167723/625000000 : ℝ)*x 0 + (5471535611/10000000000 : ℝ)*x 1 + (-1211552101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328167723/625000000 : ℝ)^5383 ≤ (45132563090267/100000000000000 : ℝ)^4359 := by
    have hnat : (328167723 : ℕ)^5383*100000000000000^4359 ≤ 45132563090267^4359*625000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328167723 625000000 45132563090267 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5471535611/10000000000 : ℝ)^5383 ≤ (593604031193/1250000000000 : ℝ)^4359 := by
    have hnat : (5471535611 : ℕ)^5383*1250000000000^4359 ≤ 593604031193^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5471535611 10000000000 593604031193 1250000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211552101/10000000000 : ℝ)^5383 ≤ (115298662557/1562500000000 : ℝ)^4359 := by
    have hnat : (1211552101 : ℕ)^5383*1562500000000^4359 ≤ 115298662557^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211552101 10000000000 115298662557 1562500000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328167723/625000000 : ℝ), (5471535611/10000000000 : ℝ), (-1211552101/10000000000 : ℝ)] ![(45132563090267/100000000000000 : ℝ), (593604031193/1250000000000 : ℝ), (115298662557/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328167723/625000000 : ℝ)|^5383 ≤ (45132563090267/100000000000000 : ℝ)^4359
        have hw : |(328167723/625000000 : ℝ)|=(328167723/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5471535611/10000000000 : ℝ)|^5383 ≤ (593604031193/1250000000000 : ℝ)^4359
        have hw : |(5471535611/10000000000 : ℝ)|=(5471535611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1211552101/10000000000 : ℝ)|^5383 ≤ (115298662557/1562500000000 : ℝ)^4359
        have hw : |(-1211552101/10000000000 : ℝ)|=(1211552101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s1_7 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (511292841/1250000000 : ℝ)*x 0 + (576373943/1250000000 : ℝ)*x 1 + (3608565767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (511292841/1250000000 : ℝ)^5383 ≤ (33155511884989/100000000000000 : ℝ)^4359 := by
    have hnat : (511292841 : ℕ)^5383*100000000000000^4359 ≤ 33155511884989^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511292841 1250000000 33155511884989 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (576373943/1250000000 : ℝ)^5383 ≤ (19221361594443/50000000000000 : ℝ)^4359 := by
    have hnat : (576373943 : ℕ)^5383*50000000000000^4359 ≤ 19221361594443^4359*1250000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576373943 1250000000 19221361594443 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3608565767/10000000000 : ℝ)^5383 ≤ (3550220612487/12500000000000 : ℝ)^4359 := by
    have hnat : (3608565767 : ℕ)^5383*12500000000000^4359 ≤ 3550220612487^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3608565767 10000000000 3550220612487 12500000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(511292841/1250000000 : ℝ), (576373943/1250000000 : ℝ), (3608565767/10000000000 : ℝ)] ![(33155511884989/100000000000000 : ℝ), (19221361594443/50000000000000 : ℝ), (3550220612487/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(511292841/1250000000 : ℝ)|^5383 ≤ (33155511884989/100000000000000 : ℝ)^4359
        have hw : |(511292841/1250000000 : ℝ)|=(511292841/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(576373943/1250000000 : ℝ)|^5383 ≤ (19221361594443/50000000000000 : ℝ)^4359
        have hw : |(576373943/1250000000 : ℝ)|=(576373943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3608565767/10000000000 : ℝ)|^5383 ≤ (3550220612487/12500000000000 : ℝ)^4359
        have hw : |(3608565767/10000000000 : ℝ)|=(3608565767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1720_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4313/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9867/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8637/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4313/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6333/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4313/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6333/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4313/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6333/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4313/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6333/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4313/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6333/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4313/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6333/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6333/100000 : ℝ) ^ (5375/1024 : ℝ) ≤ (25620648586787/50000000000000000000 : ℝ) := by
    have hpowers : (6333/100000 : ℝ)^5375 ≤ (25620648586787/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6333 : ℕ)^5375*50000000000000000000^1024 ≤ 25620648586787^1024*100000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6333 100000 25620648586787 50000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6333/100000 : ℝ)) (X := (25620648586787/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4313/20000 : ℝ) ^ (5375/1024 : ℝ) ≤ (15914951433600941/50000000000000000000 : ℝ) := by
    have hpowers : (4313/20000 : ℝ)^5375 ≤ (15914951433600941/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4313 : ℕ)^5375*50000000000000000000^1024 ≤ 15914951433600941^1024*20000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4313 20000 15914951433600941 50000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4313/20000 : ℝ)) (X := (15914951433600941/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000025620648586787/25000000000000000000 : ℝ) ≤ (10000001952411779/10000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (25000025620648586787/25000000000000000000 : ℝ)^1024 ≤ (10000001952411779/10000000000000000 : ℝ)^5375 := by
      have hnat : (25000025620648586787 : ℕ)^1024*10000000000000000^5375 ≤ 10000001952411779^5375*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000025620648586787 25000000000000000000 10000001952411779 10000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001952411779/10000000000000000 : ℝ)) (X := (25000025620648586787/25000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125996285755136733/3125000000000000000 : ℝ) ≤ (10000607294508877/10000000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (3125996285755136733/3125000000000000000 : ℝ)^1024 ≤ (10000607294508877/10000000000000000 : ℝ)^5375 := by
      have hnat : (3125996285755136733 : ℕ)^1024*10000000000000000^5375 ≤ 10000607294508877^5375*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125996285755136733 3125000000000000000 10000607294508877 10000000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000607294508877/10000000000000000 : ℝ)) (X := (3125996285755136733/3125000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015914951433600941/25000000000000000000 : ℝ) ≤ (400048505464239/400000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (25015914951433600941/25000000000000000000 : ℝ)^1024 ≤ (400048505464239/400000000000000 : ℝ)^5375 := by
      have hnat : (25015914951433600941 : ℕ)^1024*400000000000000^5375 ≤ 400048505464239^5375*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015914951433600941 25000000000000000000 400048505464239 400000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400048505464239/400000000000000 : ℝ)) (X := (25015914951433600941/25000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(25620648586787/50000000000000000000 : ℝ) ≤ ((7615618123806718723/7616000000000000000 : ℝ)+2*(302671048549/761600000000000 : ℝ)*(6333/100000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (7615618123806718723/7616000000000000000 : ℝ)+2*(302671048549/761600000000000 : ℝ)*(6333/100000 : ℝ)=(10000001952411779/10000000000000000 : ℝ) by norm_num, show 1+2*(25620648586787/50000000000000000000 : ℝ)=(25000025620648586787/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15914951433600941/50000000000000000000 : ℝ)+(25620648586787/50000000000000000000 : ℝ) ≤ ((7615618123806718723/7616000000000000000 : ℝ)+(302671048549/761600000000000 : ℝ)*((4313/20000 : ℝ)+(6333/100000 : ℝ)))^(5375/1024 : ℝ) := by
    rw [show (7615618123806718723/7616000000000000000 : ℝ)+(302671048549/761600000000000 : ℝ)*((4313/20000 : ℝ)+(6333/100000 : ℝ))=(10000607294508877/10000000000000000 : ℝ) by norm_num, show 1+(15914951433600941/50000000000000000000 : ℝ)+(25620648586787/50000000000000000000 : ℝ)=(3125996285755136733/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15914951433600941/50000000000000000000 : ℝ) ≤ ((7615618123806718723/7616000000000000000 : ℝ)+2*(302671048549/761600000000000 : ℝ)*(4313/20000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (7615618123806718723/7616000000000000000 : ℝ)+2*(302671048549/761600000000000 : ℝ)*(4313/20000 : ℝ)=(400048505464239/400000000000000 : ℝ) by norm_num, show 1+2*(15914951433600941/50000000000000000000 : ℝ)=(25015914951433600941/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7615618123806718723/7616000000000000000 : ℝ)*(X 1 0+X 2 0)+(302671048549/761600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (6333/100000 : ℝ)) (hi := (4313/20000 : ℝ)) (c := (7615618123806718723/7616000000000000000 : ℝ)) (alpha := (302671048549/761600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7615618123806718723/7616000000000000000 : ℝ)*(X 0 1+X 2 1)+(302671048549/761600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (6333/100000 : ℝ)) (hi := (4313/20000 : ℝ)) (c := (7615618123806718723/7616000000000000000 : ℝ)) (alpha := (302671048549/761600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7615618123806718723/7616000000000000000 : ℝ)*(X 0 2+X 1 2)+(302671048549/761600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (6333/100000 : ℝ)) (hi := (4313/20000 : ℝ)) (c := (7615618123806718723/7616000000000000000 : ℝ)) (alpha := (302671048549/761600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-686918579/5000000000 : ℝ)*X 0 0+(2737866373/5000000000 : ℝ)*X 0 1+(5129371553/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5343428721/10000000000 : ℝ)*X 1 0+(-1553717121/10000000000 : ℝ)*X 1 1+(5129370559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5343427523/10000000000 : ℝ)*X 2 0+(1282342859/2500000000 : ℝ)*X 2 1+(-776858781/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4089817549/10000000000 : ℝ)*X 0 0+(449515499/1250000000 : ℝ)*X 0 1+(4623239107/10000000000 : ℝ)*X 0 2+(4089817549/10000000000 : ℝ)*X 1 0+(449515499/1250000000 : ℝ)*X 1 1+(4623239107/10000000000 : ℝ)*X 1 2+(4089817549/10000000000 : ℝ)*X 2 0+(449515499/1250000000 : ℝ)*X 2 1+(4623239107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-687007883/5000000000 : ℝ)*X 0 0+(1283375319/2500000000 : ℝ)*X 0 1+(2735768047/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5250683183/10000000000 : ℝ)*X 1 0+(-605776207/5000000000 : ℝ)*X 1 1+(1367883943/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328167723/625000000 : ℝ)*X 2 0+(5471535611/10000000000 : ℝ)*X 2 1+(-1211552101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((511292841/1250000000 : ℝ)*X 0 0+(576373943/1250000000 : ℝ)*X 0 1+(3608565767/10000000000 : ℝ)*X 0 2+(511292841/1250000000 : ℝ)*X 1 0+(576373943/1250000000 : ℝ)*X 1 1+(3608565767/10000000000 : ℝ)*X 1 2+(511292841/1250000000 : ℝ)*X 2 0+(576373943/1250000000 : ℝ)*X 2 1+(3608565767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1974275163025504132906868061/190400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (41756323/4000000000000 : ℝ)*(base19) + (123810321/25000000000000 : ℝ)*(base23) + (135633871/100000000000000 : ℝ)*(lower2) + (14359587/20000000000000 : ℝ)*(upper3) + (212075161/100000000000000 : ℝ)*(lower4) + (1930386941095331/100000000000000 : ℝ)*(major0) + (1930386941095331/100000000000000 : ℝ)*(major1) + (1930386941095331/100000000000000 : ℝ)*(major2) + (1443583969744351/50000000000000 : ℝ)*(sp0) + (1443585634838639/50000000000000 : ℝ)*(sp1) + (360896157402971/12500000000000 : ℝ)*(sp2) + (121700152871111/12500000000000 : ℝ)*(sp3) + (4374096651/100000000000000 : ℝ)*(sp4) + (1279560151/50000000000000 : ℝ)*(sp6) + (121700152871111/12500000000000 : ℝ)*(f.failure) + (1443586156792677/50000000000000 : ℝ)*(f.sum) + (22772111269681/38080000000000000000000000000 : ℝ)*base66 + (8225457839030372313/761600000000000000000000000000000 : ℝ)*base67 + (6302802331267172313/761600000000000000000000000000000 : ℝ)*base69 + (8901534967772772313/761600000000000000000000000000000 : ℝ)*base71 + (695510319921/38080000000000000000000000000 : ℝ)*base74 + (5381462060943972313/761600000000000000000000000000000 : ℝ)*base75 + (4904188351766427687/761600000000000000000000000000000 : ℝ)*base78 + (1338078272707172313/761600000000000000000000000000000 : ℝ)*base79 + (91322881308879/38080000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2501619/250000000000000000000 : ℝ)*base90 + (2501619/250000000000000000000 : ℝ)*base92 + (2501619/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50267479872656841533679/9520000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1273871707/100000000000000 : ℝ)*(base19) + (1748629959/100000000000000 : ℝ)*(base23) + (114570947/100000000000000 : ℝ)*(upper2) + (25770419/20000000000000 : ℝ)*(upper3) + (76569583/25000000000000 : ℝ)*(upper5) + (494482118061819/25000000000000 : ℝ)*(major0) + (494482118061819/25000000000000 : ℝ)*(major1) + (494482118061819/25000000000000 : ℝ)*(major2) + (5154814033/50000000000000 : ℝ)*(sp1) + (12554257153/100000000000000 : ℝ)*(sp2) + (739569428495967/25000000000000 : ℝ)*(sp4) + (1479133065242047/50000000000000 : ℝ)*(sp5) + (739565852774189/25000000000000 : ℝ)*(sp6) + (31174345453253/3125000000000 : ℝ)*(sp7) + (31174345453253/3125000000000 : ℝ)*(f.failure) + (739569428495967/25000000000000 : ℝ)*(f.sum) + (45132465269369/9520000000000000000000000000 : ℝ)*base66 + (999567047031752863/190400000000000000000000000000000 : ℝ)*base68 + (277348132484552863/190400000000000000000000000000000 : ℝ)*base70 + (845616701454647137/190400000000000000000000000000000 : ℝ)*base71 + (45042904174809/9520000000000000000000000000 : ℝ)*base74 + (925449057067447137/190400000000000000000000000000000 : ℝ)*base75 + (1256447401010952863/190400000000000000000000000000000 : ℝ)*base78 + (67426164705847137/190400000000000000000000000000000 : ℝ)*base79 + (32208354030169/9520000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (769463/62500000000000000000 : ℝ)*base89 + (769463/62500000000000000000 : ℝ)*base91 + (769463/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1720_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4313/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9867/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8637/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1720_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1720_s2_0 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1376655851/10000000000 : ℝ)*x 0 + (1366021939/2500000000 : ℝ)*x 1 + (5139122591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1376655851/10000000000 : ℝ)^5383 ≤ (2160038387401/25000000000000 : ℝ)^4359 := by
    have hnat : (1376655851 : ℕ)^5383*25000000000000^4359 ≤ 2160038387401^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376655851 10000000000 2160038387401 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1366021939/2500000000 : ℝ)^5383 ≤ (47408508903601/100000000000000 : ℝ)^4359 := by
    have hnat : (1366021939 : ℕ)^5383*100000000000000^4359 ≤ 47408508903601^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366021939 2500000000 47408508903601 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139122591/10000000000 : ℝ)^5383 ≤ (21975668764333/50000000000000 : ℝ)^4359 := by
    have hnat : (5139122591 : ℕ)^5383*50000000000000^4359 ≤ 21975668764333^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139122591 10000000000 21975668764333 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1376655851/10000000000 : ℝ), (1366021939/2500000000 : ℝ), (5139122591/10000000000 : ℝ)] ![(2160038387401/25000000000000 : ℝ), (47408508903601/100000000000000 : ℝ), (21975668764333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1376655851/10000000000 : ℝ)|^5383 ≤ (2160038387401/25000000000000 : ℝ)^4359
        have hw : |(-1376655851/10000000000 : ℝ)|=(1376655851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1366021939/2500000000 : ℝ)|^5383 ≤ (47408508903601/100000000000000 : ℝ)^4359
        have hw : |(1366021939/2500000000 : ℝ)|=(1366021939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139122591/10000000000 : ℝ)|^5383 ≤ (21975668764333/50000000000000 : ℝ)^4359
        have hw : |(5139122591/10000000000 : ℝ)|=(5139122591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s2_1 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340258933/10000000000 : ℝ)*x 0 + (-309006927/2000000000 : ℝ)*x 1 + (5139122581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340258933/10000000000 : ℝ)^5383 ≤ (23042642189693/50000000000000 : ℝ)^4359 := by
    have hnat : (5340258933 : ℕ)^5383*50000000000000^4359 ≤ 23042642189693^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340258933 10000000000 23042642189693 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309006927/2000000000 : ℝ)^5383 ≤ (9963378178943/100000000000000 : ℝ)^4359 := by
    have hnat : (309006927 : ℕ)^5383*100000000000000^4359 ≤ 9963378178943^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309006927 2000000000 9963378178943 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139122581/10000000000 : ℝ)^5383 ≤ (10987834355763/25000000000000 : ℝ)^4359 := by
    have hnat : (5139122581 : ℕ)^5383*25000000000000^4359 ≤ 10987834355763^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139122581 10000000000 10987834355763 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340258933/10000000000 : ℝ), (-309006927/2000000000 : ℝ), (5139122581/10000000000 : ℝ)] ![(23042642189693/50000000000000 : ℝ), (9963378178943/100000000000000 : ℝ), (10987834355763/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340258933/10000000000 : ℝ)|^5383 ≤ (23042642189693/50000000000000 : ℝ)^4359
        have hw : |(5340258933/10000000000 : ℝ)|=(5340258933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-309006927/2000000000 : ℝ)|^5383 ≤ (9963378178943/100000000000000 : ℝ)^4359
        have hw : |(-309006927/2000000000 : ℝ)|=(309006927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139122581/10000000000 : ℝ)|^5383 ≤ (10987834355763/25000000000000 : ℝ)^4359
        have hw : |(5139122581/10000000000 : ℝ)|=(5139122581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s2_2 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5340258791/10000000000 : ℝ)*x 0 + (5139122689/10000000000 : ℝ)*x 1 + (-1545034683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5340258791/10000000000 : ℝ)^5383 ≤ (46085282866083/100000000000000 : ℝ)^4359 := by
    have hnat : (5340258791 : ℕ)^5383*100000000000000^4359 ≤ 46085282866083^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340258791 10000000000 46085282866083 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5139122689/10000000000 : ℝ)^5383 ≤ (43951338563681/100000000000000 : ℝ)^4359 := by
    have hnat : (5139122689 : ℕ)^5383*100000000000000^4359 ≤ 43951338563681^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139122689 10000000000 43951338563681 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1545034683/10000000000 : ℝ)^5383 ≤ (9963378561193/100000000000000 : ℝ)^4359 := by
    have hnat : (1545034683 : ℕ)^5383*100000000000000^4359 ≤ 9963378561193^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1545034683 10000000000 9963378561193 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5340258791/10000000000 : ℝ), (5139122689/10000000000 : ℝ), (-1545034683/10000000000 : ℝ)] ![(46085282866083/100000000000000 : ℝ), (43951338563681/100000000000000 : ℝ), (9963378561193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5340258791/10000000000 : ℝ)|^5383 ≤ (46085282866083/100000000000000 : ℝ)^4359
        have hw : |(5340258791/10000000000 : ℝ)|=(5340258791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5139122689/10000000000 : ℝ)|^5383 ≤ (43951338563681/100000000000000 : ℝ)^4359
        have hw : |(5139122689/10000000000 : ℝ)|=(5139122689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1545034683/10000000000 : ℝ)|^5383 ≤ (9963378561193/100000000000000 : ℝ)^4359
        have hw : |(-1545034683/10000000000 : ℝ)|=(1545034683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s2_3 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4092007831/10000000000 : ℝ)*x 0 + (3627657267/10000000000 : ℝ)*x 1 + (1147832093/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4092007831/10000000000 : ℝ)^5383 ≤ (33172180342629/100000000000000 : ℝ)^4359 := by
    have hnat : (4092007831 : ℕ)^5383*100000000000000^4359 ≤ 33172180342629^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4092007831 10000000000 33172180342629 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3627657267/10000000000 : ℝ)^5383 ≤ (14293720862263/50000000000000 : ℝ)^4359 := by
    have hnat : (3627657267 : ℕ)^5383*50000000000000^4359 ≤ 14293720862263^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3627657267 10000000000 14293720862263 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1147832093/2500000000 : ℝ)^5383 ≤ (2390023619191/6250000000000 : ℝ)^4359 := by
    have hnat : (1147832093 : ℕ)^5383*6250000000000^4359 ≤ 2390023619191^4359*2500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147832093 2500000000 2390023619191 6250000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4092007831/10000000000 : ℝ), (3627657267/10000000000 : ℝ), (1147832093/2500000000 : ℝ)] ![(33172180342629/100000000000000 : ℝ), (14293720862263/50000000000000 : ℝ), (2390023619191/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4092007831/10000000000 : ℝ)|^5383 ≤ (33172180342629/100000000000000 : ℝ)^4359
        have hw : |(4092007831/10000000000 : ℝ)|=(4092007831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3627657267/10000000000 : ℝ)|^5383 ≤ (14293720862263/50000000000000 : ℝ)^4359
        have hw : |(3627657267/10000000000 : ℝ)|=(3627657267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1147832093/2500000000 : ℝ)|^5383 ≤ (2390023619191/6250000000000 : ℝ)^4359
        have hw : |(1147832093/2500000000 : ℝ)|=(1147832093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s2_4 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-688400957/5000000000 : ℝ)*x 0 + (257138019/500000000 : ℝ)*x 1 + (5460395741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (688400957/5000000000 : ℝ)^5383 ≤ (8641285635071/100000000000000 : ℝ)^4359 := by
    have hnat : (688400957 : ℕ)^5383*100000000000000^4359 ≤ 8641285635071^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688400957 5000000000 8641285635071 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257138019/500000000 : ℝ)^5383 ≤ (43989760790971/100000000000000 : ℝ)^4359 := by
    have hnat : (257138019 : ℕ)^5383*100000000000000^4359 ≤ 43989760790971^4359*500000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257138019 500000000 43989760790971 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460395741/10000000000 : ℝ)^5383 ≤ (11842238390877/25000000000000 : ℝ)^4359 := by
    have hnat : (5460395741 : ℕ)^5383*25000000000000^4359 ≤ 11842238390877^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460395741 10000000000 11842238390877 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-688400957/5000000000 : ℝ), (257138019/500000000 : ℝ), (5460395741/10000000000 : ℝ)] ![(8641285635071/100000000000000 : ℝ), (43989760790971/100000000000000 : ℝ), (11842238390877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-688400957/5000000000 : ℝ)|^5383 ≤ (8641285635071/100000000000000 : ℝ)^4359
        have hw : |(-688400957/5000000000 : ℝ)|=(688400957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257138019/500000000 : ℝ)|^5383 ≤ (43989760790971/100000000000000 : ℝ)^4359
        have hw : |(257138019/500000000 : ℝ)|=(257138019/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460395741/10000000000 : ℝ)|^5383 ≤ (11842238390877/25000000000000 : ℝ)^4359
        have hw : |(5460395741/10000000000 : ℝ)|=(5460395741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s2_5 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050653493/2000000000 : ℝ)*x 0 + (-611880739/5000000000 : ℝ)*x 1 + (5460395701/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050653493/2000000000 : ℝ)^5383 ≤ (45159992215621/100000000000000 : ℝ)^4359 := by
    have hnat : (1050653493 : ℕ)^5383*100000000000000^4359 ≤ 45159992215621^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050653493 2000000000 45159992215621 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (611880739/5000000000 : ℝ)^5383 ≤ (1867763659769/25000000000000 : ℝ)^4359 := by
    have hnat : (611880739 : ℕ)^5383*25000000000000^4359 ≤ 1867763659769^4359*5000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      611880739 5000000000 1867763659769 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5460395701/10000000000 : ℝ)^5383 ≤ (2960559570937/6250000000000 : ℝ)^4359 := by
    have hnat : (5460395701 : ℕ)^5383*6250000000000^4359 ≤ 2960559570937^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460395701 10000000000 2960559570937 6250000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050653493/2000000000 : ℝ), (-611880739/5000000000 : ℝ), (5460395701/10000000000 : ℝ)] ![(45159992215621/100000000000000 : ℝ), (1867763659769/25000000000000 : ℝ), (2960559570937/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050653493/2000000000 : ℝ)|^5383 ≤ (45159992215621/100000000000000 : ℝ)^4359
        have hw : |(1050653493/2000000000 : ℝ)|=(1050653493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-611880739/5000000000 : ℝ)|^5383 ≤ (1867763659769/25000000000000 : ℝ)^4359
        have hw : |(-611880739/5000000000 : ℝ)|=(611880739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5460395701/10000000000 : ℝ)|^5383 ≤ (2960559570937/6250000000000 : ℝ)^4359
        have hw : |(5460395701/10000000000 : ℝ)|=(5460395701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s2_6 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253267449/10000000000 : ℝ)*x 0 + (54603957/100000000 : ℝ)*x 1 + (-1223761501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253267449/10000000000 : ℝ)^5383 ≤ (11289998011441/25000000000000 : ℝ)^4359 := by
    have hnat : (5253267449 : ℕ)^5383*25000000000000^4359 ≤ 11289998011441^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253267449 10000000000 11289998011441 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54603957/100000000 : ℝ)^5383 ≤ (47368953124279/100000000000000 : ℝ)^4359 := by
    have hnat : (54603957 : ℕ)^5383*100000000000000^4359 ≤ 47368953124279^4359*100000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54603957 100000000 47368953124279 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1223761501/10000000000 : ℝ)^5383 ≤ (1867763703119/25000000000000 : ℝ)^4359 := by
    have hnat : (1223761501 : ℕ)^5383*25000000000000^4359 ≤ 1867763703119^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223761501 10000000000 1867763703119 25000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253267449/10000000000 : ℝ), (54603957/100000000 : ℝ), (-1223761501/10000000000 : ℝ)] ![(11289998011441/25000000000000 : ℝ), (47368953124279/100000000000000 : ℝ), (1867763703119/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253267449/10000000000 : ℝ)|^5383 ≤ (11289998011441/25000000000000 : ℝ)^4359
        have hw : |(5253267449/10000000000 : ℝ)|=(5253267449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(54603957/100000000 : ℝ)|^5383 ≤ (47368953124279/100000000000000 : ℝ)^4359
        have hw : |(54603957/100000000 : ℝ)|=(54603957/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1223761501/10000000000 : ℝ)|^5383 ≤ (1867763703119/25000000000000 : ℝ)^4359
        have hw : |(-1223761501/10000000000 : ℝ)|=(1223761501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1720_s2_7 (p : ℝ) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (409244123/1000000000 : ℝ)*x 0 + (4580540289/10000000000 : ℝ)*x 1 + (727721269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409244123/1000000000 : ℝ)^5383 ≤ (265412153041/800000000000 : ℝ)^4359 := by
    have hnat : (409244123 : ℕ)^5383*800000000000^4359 ≤ 265412153041^4359*1000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409244123 1000000000 265412153041 800000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4580540289/10000000000 : ℝ)^5383 ≤ (19064724381417/50000000000000 : ℝ)^4359 := by
    have hnat : (4580540289 : ℕ)^5383*50000000000000^4359 ≤ 19064724381417^4359*10000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4580540289 10000000000 19064724381417 50000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (727721269/2000000000 : ℝ)^5383 ≤ (28694032082767/100000000000000 : ℝ)^4359 := by
    have hnat : (727721269 : ℕ)^5383*100000000000000^4359 ≤ 28694032082767^4359*2000000000^5383 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727721269 2000000000 28694032082767 100000000000000 5383 4359 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5383/1024 : ℝ)) 5383 4359 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(409244123/1000000000 : ℝ), (4580540289/10000000000 : ℝ), (727721269/2000000000 : ℝ)] ![(265412153041/800000000000 : ℝ), (19064724381417/50000000000000 : ℝ), (28694032082767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(409244123/1000000000 : ℝ)|^5383 ≤ (265412153041/800000000000 : ℝ)^4359
        have hw : |(409244123/1000000000 : ℝ)|=(409244123/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4580540289/10000000000 : ℝ)|^5383 ≤ (19064724381417/50000000000000 : ℝ)^4359
        have hw : |(4580540289/10000000000 : ℝ)|=(4580540289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(727721269/2000000000 : ℝ)|^5383 ≤ (28694032082767/100000000000000 : ℝ)^4359
        have hw : |(727721269/2000000000 : ℝ)|=(727721269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1720_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8637/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9867/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (63/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17029/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8637/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9867/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8637/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9867/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8637/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9867/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8637/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9867/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8637/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9867/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8637/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9867/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9867/100000 : ℝ) ^ (5375/1024 : ℝ) ≤ (262678282776571/50000000000000000000 : ℝ) := by
    have hpowers : (9867/100000 : ℝ)^5375 ≤ (262678282776571/50000000000000000000 : ℝ)^1024 := by
      have hnat : (9867 : ℕ)^5375*50000000000000000000^1024 ≤ 262678282776571^1024*100000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9867 100000 262678282776571 50000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9867/100000 : ℝ)) (X := (262678282776571/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8637/50000 : ℝ) ^ (5375/1024 : ℝ) ≤ (9932476326343203/100000000000000000000 : ℝ) := by
    have hpowers : (8637/50000 : ℝ)^5375 ≤ (9932476326343203/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8637 : ℕ)^5375*100000000000000000000^1024 ≤ 9932476326343203^1024*50000^5375 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8637 50000 9932476326343203 100000000000000000000 5375 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8637/50000 : ℝ)) (X := (9932476326343203/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000262678282776571/25000000000000000000 : ℝ) ≤ (500001000861089/500000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (25000262678282776571/25000000000000000000 : ℝ)^1024 ≤ (500001000861089/500000000000000 : ℝ)^5375 := by
      have hnat : (25000262678282776571 : ℕ)^1024*500000000000000^5375 ≤ 500001000861089^5375*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000262678282776571 25000000000000000000 500001000861089 500000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500001000861089/500000000000000 : ℝ)) (X := (25000262678282776571/25000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002091566578379269/20000000000000000000 : ℝ) ≤ (1250024903180541/1250000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (20002091566578379269/20000000000000000000 : ℝ)^1024 ≤ (1250024903180541/1250000000000000 : ℝ)^5375 := by
      have hnat : (20002091566578379269 : ℕ)^1024*1250000000000000^5375 ≤ 1250024903180541^5375*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002091566578379269 20000000000000000000 1250024903180541 1250000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250024903180541/1250000000000000 : ℝ)) (X := (20002091566578379269/20000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50009932476326343203/50000000000000000000 : ℝ) ≤ (2500094608416719/2500000000000000 : ℝ) ^ (5375/1024 : ℝ) := by
    have hpowers : (50009932476326343203/50000000000000000000 : ℝ)^1024 ≤ (2500094608416719/2500000000000000 : ℝ)^5375 := by
      have hnat : (50009932476326343203 : ℕ)^1024*2500000000000000^5375 ≤ 2500094608416719^5375*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009932476326343203 50000000000000000000 2500094608416719 2500000000000000 1024 5375 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500094608416719/2500000000000000 : ℝ)) (X := (50009932476326343203/50000000000000000000 : ℝ)) (by norm_num) 5375 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(262678282776571/50000000000000000000 : ℝ) ≤ ((6172217647708163519/6172500000000000000 : ℝ)+2*(44802055637/185175000000000 : ℝ)*(9867/100000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (6172217647708163519/6172500000000000000 : ℝ)+2*(44802055637/185175000000000 : ℝ)*(9867/100000 : ℝ)=(500001000861089/500000000000000 : ℝ) by norm_num, show 1+2*(262678282776571/50000000000000000000 : ℝ)=(25000262678282776571/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9932476326343203/100000000000000000000 : ℝ)+(262678282776571/50000000000000000000 : ℝ) ≤ ((6172217647708163519/6172500000000000000 : ℝ)+(44802055637/185175000000000 : ℝ)*((8637/50000 : ℝ)+(9867/100000 : ℝ)))^(5375/1024 : ℝ) := by
    rw [show (6172217647708163519/6172500000000000000 : ℝ)+(44802055637/185175000000000 : ℝ)*((8637/50000 : ℝ)+(9867/100000 : ℝ))=(1250024903180541/1250000000000000 : ℝ) by norm_num, show 1+(9932476326343203/100000000000000000000 : ℝ)+(262678282776571/50000000000000000000 : ℝ)=(20002091566578379269/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9932476326343203/100000000000000000000 : ℝ) ≤ ((6172217647708163519/6172500000000000000 : ℝ)+2*(44802055637/185175000000000 : ℝ)*(8637/50000 : ℝ))^(5375/1024 : ℝ) := by
    rw [show (6172217647708163519/6172500000000000000 : ℝ)+2*(44802055637/185175000000000 : ℝ)*(8637/50000 : ℝ)=(2500094608416719/2500000000000000 : ℝ) by norm_num, show 1+2*(9932476326343203/100000000000000000000 : ℝ)=(50009932476326343203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6172217647708163519/6172500000000000000 : ℝ)*(X 1 0+X 2 0)+(44802055637/185175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (9867/100000 : ℝ)) (hi := (8637/50000 : ℝ)) (c := (6172217647708163519/6172500000000000000 : ℝ)) (alpha := (44802055637/185175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6172217647708163519/6172500000000000000 : ℝ)*(X 0 1+X 2 1)+(44802055637/185175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (9867/100000 : ℝ)) (hi := (8637/50000 : ℝ)) (c := (6172217647708163519/6172500000000000000 : ℝ)) (alpha := (44802055637/185175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6172217647708163519/6172500000000000000 : ℝ)*(X 0 2+X 1 2)+(44802055637/185175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5375/1024 : ℝ)) (lo := (9867/100000 : ℝ)) (hi := (8637/50000 : ℝ)) (c := (6172217647708163519/6172500000000000000 : ℝ)) (alpha := (44802055637/185175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1376655851/10000000000 : ℝ)*X 0 0+(1366021939/2500000000 : ℝ)*X 0 1+(5139122591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5340258933/10000000000 : ℝ)*X 1 0+(-309006927/2000000000 : ℝ)*X 1 1+(5139122581/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5340258791/10000000000 : ℝ)*X 2 0+(5139122689/10000000000 : ℝ)*X 2 1+(-1545034683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4092007831/10000000000 : ℝ)*X 0 0+(3627657267/10000000000 : ℝ)*X 0 1+(1147832093/2500000000 : ℝ)*X 0 2+(4092007831/10000000000 : ℝ)*X 1 0+(3627657267/10000000000 : ℝ)*X 1 1+(1147832093/2500000000 : ℝ)*X 1 2+(4092007831/10000000000 : ℝ)*X 2 0+(3627657267/10000000000 : ℝ)*X 2 1+(1147832093/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-688400957/5000000000 : ℝ)*X 0 0+(257138019/500000000 : ℝ)*X 0 1+(5460395741/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050653493/2000000000 : ℝ)*X 1 0+(-611880739/5000000000 : ℝ)*X 1 1+(5460395701/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5253267449/10000000000 : ℝ)*X 2 0+(54603957/100000000 : ℝ)*X 2 1+(-1223761501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((409244123/1000000000 : ℝ)*X 0 0+(4580540289/10000000000 : ℝ)*X 0 1+(727721269/2000000000 : ℝ)*X 0 2+(409244123/1000000000 : ℝ)*X 1 0+(4580540289/10000000000 : ℝ)*X 1 1+(727721269/2000000000 : ℝ)*X 1 2+(409244123/1000000000 : ℝ)*X 2 0+(4580540289/10000000000 : ℝ)*X 2 1+(727721269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1720_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56631506575495661180455753/15431250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (860549/160000000000 : ℝ)*(base19) + (27582123/6250000000000 : ℝ)*(base23) + (118029049/100000000000000 : ℝ)*(upper3) + (3925973/50000000000000 : ℝ)*(upper4) + (2689597/4000000000000 : ℝ)*(upper5) + (205748275181579/10000000000000 : ℝ)*(major0) + (205748275181579/10000000000000 : ℝ)*(major1) + (205748275181579/10000000000000 : ℝ)*(major2) + (307725832230547/10000000000000 : ℝ)*(sp0) + (3077262152478717/100000000000000 : ℝ)*(sp1) + (1538631124503937/50000000000000 : ℝ)*(sp2) + (518850214636331/50000000000000 : ℝ)*(sp3) + (1092004093/25000000000000 : ℝ)*(sp4) + (141356643/6250000000000 : ℝ)*(sp7) + (1037702690978949/100000000000000 : ℝ)*(f.failure) + (1538631345160921/50000000000000 : ℝ)*(f.sum) + (839375839397/231468750000000000000000000 : ℝ)*base66 + (1053995105348400497/185175000000000000000000000000000 : ℝ)*base68 + (76783925289900497/185175000000000000000000000000000 : ℝ)*base70 + (1084504660008375497/185175000000000000000000000000000 : ℝ)*base72 + (25157004287653/7407000000000000000000000000 : ℝ)*base74 + (1056297485192025497/185175000000000000000000000000000 : ℝ)*base76 + (99672544996349503/185175000000000000000000000000000 : ℝ)*base77 + (2087509834096950497/185175000000000000000000000000000 : ℝ)*base80 + (816283524799/740700000000000000000000000 : ℝ)*base82 + (7374121/2000000000000000000000 : ℝ)*base90 + (7374121/2000000000000000000000 : ℝ)*base92 + (7374121/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106951054519820767593019/12345000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1198635479/100000000000000 : ℝ)*(base19) + (637895619/50000000000000 : ℝ)*(base23) + (182100759/100000000000000 : ℝ)*(upper3) + (20790501/50000000000000 : ℝ)*(lower4) + (93075127/50000000000000 : ℝ)*(upper5) + (1052477317507901/50000000000000 : ℝ)*(major0) + (1052477317507901/50000000000000 : ℝ)*(major1) + (1052477317507901/50000000000000 : ℝ)*(major2) + (271917601/2500000000000 : ℝ)*(sp1) + (354224359/3125000000000 : ℝ)*(sp2) + (629652717211921/20000000000000 : ℝ)*(sp4) + (3148251510720087/100000000000000 : ℝ)*(sp5) + (3148250975088879/100000000000000 : ℝ)*(sp6) + (1061645395188263/100000000000000 : ℝ)*(sp7) + (1061645395188263/100000000000000 : ℝ)*(f.failure) + (629652717211921/20000000000000 : ℝ)*(f.sum) + (15223854810037/4629375000000000000000000000 : ℝ)*base65 + (3231812044097465857/925875000000000000000000000000000 : ℝ)*base67 + (1417925847918909143/925875000000000000000000000000000 : ℝ)*base70 + (590971781634215857/925875000000000000000000000000000 : ℝ)*base71 + (150515388135761/37035000000000000000000000000 : ℝ)*base73 + (4355663265325659143/925875000000000000000000000000000 : ℝ)*base76 + (2484062696981784143/925875000000000000000000000000000 : ℝ)*base78 + (7152731907569465857/925875000000000000000000000000000 : ℝ)*base79 + (23498392921831/9258750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6499827/2000000000000000000000 : ℝ)*base90 + (6499827/2000000000000000000000 : ℝ)*base92 + (6499827/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1720_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8637/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9867/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17029/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1720_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1720_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17029/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1720_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1720_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1720_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5375/1024 : ℝ) ≤ p) (hpb : p ≤ (5383/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39654571/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (63/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17029/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1720_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
