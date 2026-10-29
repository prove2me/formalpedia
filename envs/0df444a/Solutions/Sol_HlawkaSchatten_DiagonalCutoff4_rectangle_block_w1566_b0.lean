-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1566_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:25:54.755853+00:00
-- url     : https://prove2.me/submissions/686e13be-337f-41e2-858d-e0f184efbfd5

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
theorem support_rectangle_w1566_s0_0 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1630028467/10000000000 : ℝ)*x 0 + (2936222229/5000000000 : ℝ)*x 1 + (2438871851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1630028467/10000000000 : ℝ)^4629 ≤ (4868434052457/50000000000000 : ℝ)^3605 := by
    have hnat : (1630028467 : ℕ)^4629*50000000000000^3605 ≤ 4868434052457^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1630028467 10000000000 4868434052457 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2936222229/5000000000 : ℝ)^4629 ≤ (25241894768987/50000000000000 : ℝ)^3605 := by
    have hnat : (2936222229 : ℕ)^4629*50000000000000^3605 ≤ 25241894768987^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2936222229 5000000000 25241894768987 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2438871851/5000000000 : ℝ)^4629 ≤ (39779342344769/100000000000000 : ℝ)^3605 := by
    have hnat : (2438871851 : ℕ)^4629*100000000000000^3605 ≤ 39779342344769^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438871851 5000000000 39779342344769 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1630028467/10000000000 : ℝ), (2936222229/5000000000 : ℝ), (2438871851/5000000000 : ℝ)] ![(4868434052457/50000000000000 : ℝ), (25241894768987/50000000000000 : ℝ), (39779342344769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1630028467/10000000000 : ℝ)|^4629 ≤ (4868434052457/50000000000000 : ℝ)^3605
        have hw : |(-1630028467/10000000000 : ℝ)|=(1630028467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2936222229/5000000000 : ℝ)|^4629 ≤ (25241894768987/50000000000000 : ℝ)^3605
        have hw : |(2936222229/5000000000 : ℝ)|=(2936222229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2438871851/5000000000 : ℝ)|^4629 ≤ (39779342344769/100000000000000 : ℝ)^3605
        have hw : |(2438871851/5000000000 : ℝ)|=(2438871851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s0_1 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (341645773/625000000 : ℝ)*x 0 + (-2183827293/10000000000 : ℝ)*x 1 + (975548741/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (341645773/625000000 : ℝ)^4629 ≤ (46045650339/100000000000 : ℝ)^3605 := by
    have hnat : (341645773 : ℕ)^4629*100000000000^3605 ≤ 46045650339^3605*625000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341645773 625000000 46045650339 100000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2183827293/10000000000 : ℝ)^4629 ≤ (2835001454217/20000000000000 : ℝ)^3605 := by
    have hnat : (2183827293 : ℕ)^4629*20000000000000^3605 ≤ 2835001454217^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183827293 10000000000 2835001454217 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (975548741/2000000000 : ℝ)^4629 ≤ (4972417797023/12500000000000 : ℝ)^3605 := by
    have hnat : (975548741 : ℕ)^4629*12500000000000^3605 ≤ 4972417797023^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975548741 2000000000 4972417797023 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(341645773/625000000 : ℝ), (-2183827293/10000000000 : ℝ), (975548741/2000000000 : ℝ)] ![(46045650339/100000000000 : ℝ), (2835001454217/20000000000000 : ℝ), (4972417797023/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(341645773/625000000 : ℝ)|^4629 ≤ (46045650339/100000000000 : ℝ)^3605
        have hw : |(341645773/625000000 : ℝ)|=(341645773/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2183827293/10000000000 : ℝ)|^4629 ≤ (2835001454217/20000000000000 : ℝ)^3605
        have hw : |(-2183827293/10000000000 : ℝ)|=(2183827293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(975548741/2000000000 : ℝ)|^4629 ≤ (4972417797023/12500000000000 : ℝ)^3605
        have hw : |(975548741/2000000000 : ℝ)|=(975548741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s0_2 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (273316621/500000000 : ℝ)*x 0 + (975548729/2000000000 : ℝ)*x 1 + (-2183827301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273316621/500000000 : ℝ)^4629 ≤ (46045650901443/100000000000000 : ℝ)^3605 := by
    have hnat : (273316621 : ℕ)^4629*100000000000000^3605 ≤ 46045650901443^3605*500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273316621 500000000 46045650901443 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975548729/2000000000 : ℝ)^4629 ≤ (19889670873939/50000000000000 : ℝ)^3605 := by
    have hnat : (975548729 : ℕ)^4629*50000000000000^3605 ≤ 19889670873939^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975548729 2000000000 19889670873939 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2183827301/10000000000 : ℝ)^4629 ≤ (7087503668881/50000000000000 : ℝ)^3605 := by
    have hnat : (2183827301 : ℕ)^4629*50000000000000^3605 ≤ 7087503668881^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2183827301 10000000000 7087503668881 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(273316621/500000000 : ℝ), (975548729/2000000000 : ℝ), (-2183827301/10000000000 : ℝ)] ![(46045650901443/100000000000000 : ℝ), (19889670873939/50000000000000 : ℝ), (7087503668881/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(273316621/500000000 : ℝ)|^4629 ≤ (46045650901443/100000000000000 : ℝ)^3605
        have hw : |(273316621/500000000 : ℝ)|=(273316621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(975548729/2000000000 : ℝ)|^4629 ≤ (19889670873939/50000000000000 : ℝ)^3605
        have hw : |(975548729/2000000000 : ℝ)|=(975548729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2183827301/10000000000 : ℝ)|^4629 ≤ (7087503668881/50000000000000 : ℝ)^3605
        have hw : |(-2183827301/10000000000 : ℝ)|=(2183827301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s0_3 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4130884341/10000000000 : ℝ)*x 0 + (3092943487/10000000000 : ℝ)*x 1 + (5434599347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4130884341/10000000000 : ℝ)^4629 ≤ (1285405274637/4000000000000 : ℝ)^3605 := by
    have hnat : (4130884341 : ℕ)^4629*4000000000000^3605 ≤ 1285405274637^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130884341 10000000000 1285405274637 4000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3092943487/10000000000 : ℝ)^4629 ≤ (22162164924873/100000000000000 : ℝ)^3605 := by
    have hnat : (3092943487 : ℕ)^4629*100000000000000^3605 ≤ 22162164924873^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3092943487 10000000000 22162164924873 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434599347/10000000000 : ℝ)^4629 ≤ (22851351595659/50000000000000 : ℝ)^3605 := by
    have hnat : (5434599347 : ℕ)^4629*50000000000000^3605 ≤ 22851351595659^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434599347 10000000000 22851351595659 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4130884341/10000000000 : ℝ), (3092943487/10000000000 : ℝ), (5434599347/10000000000 : ℝ)] ![(1285405274637/4000000000000 : ℝ), (22162164924873/100000000000000 : ℝ), (22851351595659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4130884341/10000000000 : ℝ)|^4629 ≤ (1285405274637/4000000000000 : ℝ)^3605
        have hw : |(4130884341/10000000000 : ℝ)|=(4130884341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3092943487/10000000000 : ℝ)|^4629 ≤ (22162164924873/100000000000000 : ℝ)^3605
        have hw : |(3092943487/10000000000 : ℝ)|=(3092943487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434599347/10000000000 : ℝ)|^4629 ≤ (22851351595659/50000000000000 : ℝ)^3605
        have hw : |(5434599347/10000000000 : ℝ)|=(5434599347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s0_4 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1633113351/10000000000 : ℝ)*x 0 + (2451417049/5000000000 : ℝ)*x 1 + (5846464661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1633113351/10000000000 : ℝ)^4629 ≤ (9760536102277/100000000000000 : ℝ)^3605 := by
    have hnat : (1633113351 : ℕ)^4629*100000000000000^3605 ≤ 9760536102277^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1633113351 10000000000 9760536102277 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2451417049/5000000000 : ℝ)^4629 ≤ (20021137589123/50000000000000 : ℝ)^3605 := by
    have hnat : (2451417049 : ℕ)^4629*50000000000000^3605 ≤ 20021137589123^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2451417049 5000000000 20021137589123 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5846464661/10000000000 : ℝ)^4629 ≤ (12549297176999/25000000000000 : ℝ)^3605 := by
    have hnat : (5846464661 : ℕ)^4629*25000000000000^3605 ≤ 12549297176999^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5846464661 10000000000 12549297176999 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1633113351/10000000000 : ℝ), (2451417049/5000000000 : ℝ), (5846464661/10000000000 : ℝ)] ![(9760536102277/100000000000000 : ℝ), (20021137589123/50000000000000 : ℝ), (12549297176999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1633113351/10000000000 : ℝ)|^4629 ≤ (9760536102277/100000000000000 : ℝ)^3605
        have hw : |(-1633113351/10000000000 : ℝ)|=(1633113351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2451417049/5000000000 : ℝ)|^4629 ≤ (20021137589123/50000000000000 : ℝ)^3605
        have hw : |(2451417049/5000000000 : ℝ)|=(2451417049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5846464661/10000000000 : ℝ)|^4629 ≤ (12549297176999/25000000000000 : ℝ)^3605
        have hw : |(5846464661/10000000000 : ℝ)|=(5846464661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s0_5 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5194411793/10000000000 : ℝ)*x 0 + (-607553691/5000000000 : ℝ)*x 1 + (1461616089/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5194411793/10000000000 : ℝ)^4629 ≤ (10781383931887/25000000000000 : ℝ)^3605 := by
    have hnat : (5194411793 : ℕ)^4629*25000000000000^3605 ≤ 10781383931887^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194411793 10000000000 10781383931887 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (607553691/5000000000 : ℝ)^4629 ≤ (26083120721/390625000000 : ℝ)^3605 := by
    have hnat : (607553691 : ℕ)^4629*390625000000^3605 ≤ 26083120721^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      607553691 5000000000 26083120721 390625000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1461616089/2500000000 : ℝ)^4629 ≤ (50197185345453/100000000000000 : ℝ)^3605 := by
    have hnat : (1461616089 : ℕ)^4629*100000000000000^3605 ≤ 50197185345453^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461616089 2500000000 50197185345453 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5194411793/10000000000 : ℝ), (-607553691/5000000000 : ℝ), (1461616089/2500000000 : ℝ)] ![(10781383931887/25000000000000 : ℝ), (26083120721/390625000000 : ℝ), (50197185345453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5194411793/10000000000 : ℝ)|^4629 ≤ (10781383931887/25000000000000 : ℝ)^3605
        have hw : |(5194411793/10000000000 : ℝ)|=(5194411793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-607553691/5000000000 : ℝ)|^4629 ≤ (26083120721/390625000000 : ℝ)^3605
        have hw : |(-607553691/5000000000 : ℝ)|=(607553691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1461616089/2500000000 : ℝ)|^4629 ≤ (50197185345453/100000000000000 : ℝ)^3605
        have hw : |(1461616089/2500000000 : ℝ)|=(1461616089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s0_6 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2597205929/5000000000 : ℝ)*x 0 + (2923232499/5000000000 : ℝ)*x 1 + (-1215106281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2597205929/5000000000 : ℝ)^4629 ≤ (10781384105121/25000000000000 : ℝ)^3605 := by
    have hnat : (2597205929 : ℕ)^4629*25000000000000^3605 ≤ 10781384105121^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2597205929 5000000000 10781384105121 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2923232499/5000000000 : ℝ)^4629 ≤ (5019719242333/10000000000000 : ℝ)^3605 := by
    have hnat : (2923232499 : ℕ)^4629*10000000000000^3605 ≤ 5019719242333^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2923232499 5000000000 5019719242333 10000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1215106281/10000000000 : ℝ)^4629 ≤ (3338635567887/50000000000000 : ℝ)^3605 := by
    have hnat : (1215106281 : ℕ)^4629*50000000000000^3605 ≤ 3338635567887^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215106281 10000000000 3338635567887 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2597205929/5000000000 : ℝ), (2923232499/5000000000 : ℝ), (-1215106281/10000000000 : ℝ)] ![(10781384105121/25000000000000 : ℝ), (5019719242333/10000000000000 : ℝ), (3338635567887/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2597205929/5000000000 : ℝ)|^4629 ≤ (10781384105121/25000000000000 : ℝ)^3605
        have hw : |(2597205929/5000000000 : ℝ)|=(2597205929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2923232499/5000000000 : ℝ)|^4629 ≤ (5019719242333/10000000000000 : ℝ)^3605
        have hw : |(2923232499/5000000000 : ℝ)|=(2923232499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1215106281/10000000000 : ℝ)|^4629 ≤ (3338635567887/50000000000000 : ℝ)^3605
        have hw : |(-1215106281/10000000000 : ℝ)|=(1215106281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s0_7 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4138144243/10000000000 : ℝ)*x 0 + (2687766797/5000000000 : ℝ)*x 1 + (788525813/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4138144243/10000000000 : ℝ)^4629 ≤ (32207668611017/100000000000000 : ℝ)^3605 := by
    have hnat : (4138144243 : ℕ)^4629*100000000000000^3605 ≤ 32207668611017^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4138144243 10000000000 32207668611017 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687766797/5000000000 : ℝ)^4629 ≤ (45065879266669/100000000000000 : ℝ)^3605 := by
    have hnat : (2687766797 : ℕ)^4629*100000000000000^3605 ≤ 45065879266669^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687766797 5000000000 45065879266669 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (788525813/2500000000 : ℝ)^4629 ≤ (11363226055131/50000000000000 : ℝ)^3605 := by
    have hnat : (788525813 : ℕ)^4629*50000000000000^3605 ≤ 11363226055131^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788525813 2500000000 11363226055131 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4138144243/10000000000 : ℝ), (2687766797/5000000000 : ℝ), (788525813/2500000000 : ℝ)] ![(32207668611017/100000000000000 : ℝ), (45065879266669/100000000000000 : ℝ), (11363226055131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4138144243/10000000000 : ℝ)|^4629 ≤ (32207668611017/100000000000000 : ℝ)^3605
        have hw : |(4138144243/10000000000 : ℝ)|=(4138144243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687766797/5000000000 : ℝ)|^4629 ≤ (45065879266669/100000000000000 : ℝ)^3605
        have hw : |(2687766797/5000000000 : ℝ)|=(2687766797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(788525813/2500000000 : ℝ)|^4629 ≤ (11363226055131/50000000000000 : ℝ)^3605
        have hw : |(788525813/2500000000 : ℝ)|=(788525813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1566_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3497/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24803/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4627/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4627 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4627*1^1024 ≤ 0^1024*1^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4627/1024 : ℝ) ≤ (79589598308350467/5000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4627 ≤ (79589598308350467/5000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4627*5000000000000000000^1024 ≤ 79589598308350467^1024*5^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 79589598308350467 5000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (79589598308350467/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4627 := by
      have hnat : (1 : ℕ)^1024*1^4627 ≤ 1^4627*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (5079589598308350467/5000000000000000000 : ℝ) ≤ (5017505805831623/5000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (5079589598308350467/5000000000000000000 : ℝ)^1024 ≤ (5017505805831623/5000000000000000 : ℝ)^4627 := by
      have hnat : (5079589598308350467 : ℕ)^1024*5000000000000000^4627 ≤ 5017505805831623^4627*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5079589598308350467 5000000000000000000 5017505805831623 5000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5017505805831623/5000000000000000 : ℝ)) (X := (5079589598308350467/5000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2579589598308350467/2500000000000000000 : ℝ) ≤ (2517505805831623/2500000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (2579589598308350467/2500000000000000000 : ℝ)^1024 ≤ (2517505805831623/2500000000000000 : ℝ)^4627 := by
      have hnat : (2579589598308350467 : ℕ)^1024*2500000000000000^4627 ≤ 2517505805831623^4627*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2579589598308350467 2500000000000000000 2517505805831623 2500000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2517505805831623/2500000000000000 : ℝ)) (X := (2579589598308350467/2500000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(17505805831623/2000000000000000 : ℝ)*(0 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17505805831623/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(79589598308350467/5000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(17505805831623/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4627/1024 : ℝ) := by
    rw [show (1 : ℝ)+(17505805831623/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5017505805831623/5000000000000000 : ℝ) by norm_num, show 1+(79589598308350467/5000000000000000000 : ℝ)+(0 : ℝ)=(5079589598308350467/5000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(79589598308350467/5000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(17505805831623/2000000000000000 : ℝ)*(2/5 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(17505805831623/2000000000000000 : ℝ)*(2/5 : ℝ)=(2517505805831623/2500000000000000 : ℝ) by norm_num, show 1+2*(79589598308350467/5000000000000000000 : ℝ)=(2579589598308350467/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(17505805831623/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17505805831623/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(17505805831623/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17505805831623/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(17505805831623/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (17505805831623/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1630028467/10000000000 : ℝ)*X 0 0+(2936222229/5000000000 : ℝ)*X 0 1+(2438871851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((341645773/625000000 : ℝ)*X 1 0+(-2183827293/10000000000 : ℝ)*X 1 1+(975548741/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((273316621/500000000 : ℝ)*X 2 0+(975548729/2000000000 : ℝ)*X 2 1+(-2183827301/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4130884341/10000000000 : ℝ)*X 0 0+(3092943487/10000000000 : ℝ)*X 0 1+(5434599347/10000000000 : ℝ)*X 0 2+(4130884341/10000000000 : ℝ)*X 1 0+(3092943487/10000000000 : ℝ)*X 1 1+(5434599347/10000000000 : ℝ)*X 1 2+(4130884341/10000000000 : ℝ)*X 2 0+(3092943487/10000000000 : ℝ)*X 2 1+(5434599347/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1633113351/10000000000 : ℝ)*X 0 0+(2451417049/5000000000 : ℝ)*X 0 1+(5846464661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5194411793/10000000000 : ℝ)*X 1 0+(-607553691/5000000000 : ℝ)*X 1 1+(1461616089/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2597205929/5000000000 : ℝ)*X 2 0+(2923232499/5000000000 : ℝ)*X 2 1+(-1215106281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4138144243/10000000000 : ℝ)*X 0 0+(2687766797/5000000000 : ℝ)*X 0 1+(788525813/2500000000 : ℝ)*X 0 2+(4138144243/10000000000 : ℝ)*X 1 0+(2687766797/5000000000 : ℝ)*X 1 1+(788525813/2500000000 : ℝ)*X 1 2+(4138144243/10000000000 : ℝ)*X 2 0+(2687766797/5000000000 : ℝ)*X 2 1+(788525813/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101371895750986150155657/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38258637/100000000000000 : ℝ)*(base1) + (829304721/100000000000000 : ℝ)*(base19) + (33554729/4000000000000 : ℝ)*(base23) + (13371423/12500000000000 : ℝ)*(upper3) + (107222909/100000000000000 : ℝ)*(upper5) + (358096102420453/50000000000000 : ℝ)*(major0) + (358096102420453/50000000000000 : ℝ)*(major1) + (358096102420453/50000000000000 : ℝ)*(major2) + (1005330394247213/100000000000000 : ℝ)*(sp0) + (1005332617974109/100000000000000 : ℝ)*(sp1) + (251333152102651/25000000000000 : ℝ)*(sp2) + (42704947564611/10000000000000 : ℝ)*(sp3) + (3091290253/100000000000000 : ℝ)*(sp4) + (1313335701/100000000000000 : ℝ)*(sp7) + (427050827240447/100000000000000 : ℝ)*(f.failure) + (100533344727883/10000000000000 : ℝ)*(f.sum) + (199797259564781/50000000000000000000000000000 : ℝ)*base66 + (192153861814781/100000000000000000000000000000 : ℝ)*base68 + (173118711285219/100000000000000000000000000000 : ℝ)*base69 + (315661427114781/100000000000000000000000000000 : ℝ)*base72 + (85030531964781/50000000000000000000000000000 : ℝ)*base74 + (699649497314781/100000000000000000000000000000 : ℝ)*base76 + (186093583914781/100000000000000000000000000000 : ℝ)*base78 + (115409214985219/100000000000000000000000000000 : ℝ)*base79 + (29823368485219/50000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (40412597/10000000000000000000000 : ℝ)*base90 + (40412597/10000000000000000000000 : ℝ)*base92 + (40412597/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (119861903817269052085527/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19533589/20000000000000 : ℝ)*(base19) + (250526101/50000000000000 : ℝ)*(base23) + (54784319/20000000000000 : ℝ)*(base39) + (2210031/5000000000000 : ℝ)*(upper2) + (169864923/100000000000000 : ℝ)*(upper5) + (377473846738713/50000000000000 : ℝ)*(major0) + (377473846738713/50000000000000 : ℝ)*(major1) + (754947419555831/100000000000000 : ℝ)*(major2) + (85110283/100000000000000 : ℝ)*(sp1) + (383775209/50000000000000 : ℝ)*(sp2) + (529867548612979/50000000000000 : ℝ)*(sp4) + (105973491444773/10000000000000 : ℝ)*(sp5) + (1059734102544933/100000000000000 : ℝ)*(sp6) + (450159935899359/100000000000000 : ℝ)*(sp7) + (450159935899359/100000000000000 : ℝ)*(f.failure) + (1059735371147553/100000000000000 : ℝ)*(f.sum) + (620792054513889/200000000000000000000000000000 : ℝ)*base66 + (1398144192156287/200000000000000000000000000000 : ℝ)*base68 + (305973216878801/100000000000000000000000000000 : ℝ)*base70 + (1013979820356287/200000000000000000000000000000 : ℝ)*base72 + (701070952113889/200000000000000000000000000000 : ℝ)*base74 + (48499232578801/100000000000000000000000000000 : ℝ)*base76 + (603845377378801/100000000000000000000000000000 : ℝ)*base78 + (74516145278801/100000000000000000000000000000 : ℝ)*base80 + (64986120128801/50000000000000000000000000000 : ℝ)*base82 + (109202091/10000000000000000000000 : ℝ)*base89 + (109202091/10000000000000000000000 : ℝ)*base91 + (109202091/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1566_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3497/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24803/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1566_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1566_s1_0 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-353929473/2000000000 : ℝ)*x 0 + (86517347/156250000 : ℝ)*x 1 + (1280776369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (353929473/2000000000 : ℝ)^4629 ≤ (10820541939297/100000000000000 : ℝ)^3605 := by
    have hnat : (353929473 : ℕ)^4629*100000000000000^3605 ≤ 10820541939297^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      353929473 2000000000 10820541939297 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86517347/156250000 : ℝ)^4629 ≤ (23406300343309/50000000000000 : ℝ)^3605 := by
    have hnat : (86517347 : ℕ)^4629*50000000000000^3605 ≤ 23406300343309^3605*156250000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86517347 156250000 23406300343309 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1280776369/2500000000 : ℝ)^4629 ≤ (21183428680351/50000000000000 : ℝ)^3605 := by
    have hnat : (1280776369 : ℕ)^4629*50000000000000^3605 ≤ 21183428680351^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1280776369 2500000000 21183428680351 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-353929473/2000000000 : ℝ), (86517347/156250000 : ℝ), (1280776369/2500000000 : ℝ)] ![(10820541939297/100000000000000 : ℝ), (23406300343309/50000000000000 : ℝ), (21183428680351/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-353929473/2000000000 : ℝ)|^4629 ≤ (10820541939297/100000000000000 : ℝ)^3605
        have hw : |(-353929473/2000000000 : ℝ)|=(353929473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86517347/156250000 : ℝ)|^4629 ≤ (23406300343309/50000000000000 : ℝ)^3605
        have hw : |(86517347/156250000 : ℝ)|=(86517347/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1280776369/2500000000 : ℝ)|^4629 ≤ (21183428680351/50000000000000 : ℝ)^3605
        have hw : |(1280776369/2500000000 : ℝ)|=(1280776369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s1_1 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5377114329/10000000000 : ℝ)*x 0 + (-1986292057/10000000000 : ℝ)*x 1 + (5123105337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377114329/10000000000 : ℝ)^4629 ≤ (22541448180101/50000000000000 : ℝ)^3605 := by
    have hnat : (5377114329 : ℕ)^4629*50000000000000^3605 ≤ 22541448180101^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377114329 10000000000 22541448180101 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1986292057/10000000000 : ℝ)^4629 ≤ (12550247740051/100000000000000 : ℝ)^3605 := by
    have hnat : (1986292057 : ℕ)^4629*100000000000000^3605 ≤ 12550247740051^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1986292057 10000000000 12550247740051 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5123105337/10000000000 : ℝ)^4629 ≤ (42366855884691/100000000000000 : ℝ)^3605 := by
    have hnat : (5123105337 : ℕ)^4629*100000000000000^3605 ≤ 42366855884691^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123105337 10000000000 42366855884691 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377114329/10000000000 : ℝ), (-1986292057/10000000000 : ℝ), (5123105337/10000000000 : ℝ)] ![(22541448180101/50000000000000 : ℝ), (12550247740051/100000000000000 : ℝ), (42366855884691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377114329/10000000000 : ℝ)|^4629 ≤ (22541448180101/50000000000000 : ℝ)^3605
        have hw : |(5377114329/10000000000 : ℝ)|=(5377114329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1986292057/10000000000 : ℝ)|^4629 ≤ (12550247740051/100000000000000 : ℝ)^3605
        have hw : |(-1986292057/10000000000 : ℝ)|=(1986292057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5123105337/10000000000 : ℝ)|^4629 ≤ (42366855884691/100000000000000 : ℝ)^3605
        have hw : |(5123105337/10000000000 : ℝ)|=(5123105337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s1_2 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2688557117/5000000000 : ℝ)*x 0 + (512310579/1000000000 : ℝ)*x 1 + (-198629159/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2688557117/5000000000 : ℝ)^4629 ≤ (9016579067491/20000000000000 : ℝ)^3605 := by
    have hnat : (2688557117 : ℕ)^4629*20000000000000^3605 ≤ 9016579067491^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688557117 5000000000 9016579067491 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512310579/1000000000 : ℝ)^4629 ≤ (42366860695001/100000000000000 : ℝ)^3605 := by
    have hnat : (512310579 : ℕ)^4629*100000000000000^3605 ≤ 42366860695001^3605*1000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512310579 1000000000 42366860695001 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198629159/1000000000 : ℝ)^4629 ≤ (3137560987799/25000000000000 : ℝ)^3605 := by
    have hnat : (198629159 : ℕ)^4629*25000000000000^3605 ≤ 3137560987799^3605*1000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198629159 1000000000 3137560987799 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2688557117/5000000000 : ℝ), (512310579/1000000000 : ℝ), (-198629159/1000000000 : ℝ)] ![(9016579067491/20000000000000 : ℝ), (42366860695001/100000000000000 : ℝ), (3137560987799/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2688557117/5000000000 : ℝ)|^4629 ≤ (9016579067491/20000000000000 : ℝ)^3605
        have hw : |(2688557117/5000000000 : ℝ)|=(2688557117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512310579/1000000000 : ℝ)|^4629 ≤ (42366860695001/100000000000000 : ℝ)^3605
        have hw : |(512310579/1000000000 : ℝ)|=(512310579/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-198629159/1000000000 : ℝ)|^4629 ≤ (3137560987799/25000000000000 : ℝ)^3605
        have hw : |(-198629159/1000000000 : ℝ)|=(198629159/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s1_3 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057479301/2500000000 : ℝ)*x 0 + (150612201/400000000 : ℝ)*x 1 + (473992767/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057479301/2500000000 : ℝ)^4629 ≤ (6625542664373/20000000000000 : ℝ)^3605 := by
    have hnat : (1057479301 : ℕ)^4629*20000000000000^3605 ≤ 6625542664373^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057479301 2500000000 6625542664373 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150612201/400000000 : ℝ)^4629 ≤ (14265146436391/50000000000000 : ℝ)^3605 := by
    have hnat : (150612201 : ℕ)^4629*50000000000000^3605 ≤ 14265146436391^3605*400000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150612201 400000000 14265146436391 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473992767/1000000000 : ℝ)^4629 ≤ (7668398757767/20000000000000 : ℝ)^3605 := by
    have hnat : (473992767 : ℕ)^4629*20000000000000^3605 ≤ 7668398757767^3605*1000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473992767 1000000000 7668398757767 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057479301/2500000000 : ℝ), (150612201/400000000 : ℝ), (473992767/1000000000 : ℝ)] ![(6625542664373/20000000000000 : ℝ), (14265146436391/50000000000000 : ℝ), (7668398757767/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057479301/2500000000 : ℝ)|^4629 ≤ (6625542664373/20000000000000 : ℝ)^3605
        have hw : |(1057479301/2500000000 : ℝ)|=(1057479301/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150612201/400000000 : ℝ)|^4629 ≤ (14265146436391/50000000000000 : ℝ)^3605
        have hw : |(150612201/400000000 : ℝ)|=(150612201/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(473992767/1000000000 : ℝ)|^4629 ≤ (7668398757767/20000000000000 : ℝ)^3605
        have hw : |(473992767/1000000000 : ℝ)|=(473992767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s1_4 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-442465939/2500000000 : ℝ)*x 0 + (512739999/1000000000 : ℝ)*x 1 + (138318799/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442465939/2500000000 : ℝ)^4629 ≤ (10822240929703/100000000000000 : ℝ)^3605 := by
    have hnat : (442465939 : ℕ)^4629*100000000000000^3605 ≤ 10822240929703^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442465939 2500000000 10822240929703 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512739999/1000000000 : ℝ)^4629 ≤ (1060311632839/2500000000000 : ℝ)^3605 := by
    have hnat : (512739999 : ℕ)^4629*2500000000000^3605 ≤ 1060311632839^3605*1000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512739999 1000000000 1060311632839 2500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138318799/250000000 : ℝ)^4629 ≤ (9353058748557/20000000000000 : ℝ)^3605 := by
    have hnat : (138318799 : ℕ)^4629*20000000000000^3605 ≤ 9353058748557^3605*250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138318799 250000000 9353058748557 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-442465939/2500000000 : ℝ), (512739999/1000000000 : ℝ), (138318799/250000000 : ℝ)] ![(10822240929703/100000000000000 : ℝ), (1060311632839/2500000000000 : ℝ), (9353058748557/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-442465939/2500000000 : ℝ)|^4629 ≤ (10822240929703/100000000000000 : ℝ)^3605
        have hw : |(-442465939/2500000000 : ℝ)|=(442465939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512739999/1000000000 : ℝ)|^4629 ≤ (1060311632839/2500000000000 : ℝ)^3605
        have hw : |(512739999/1000000000 : ℝ)|=(512739999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138318799/250000000 : ℝ)|^4629 ≤ (9353058748557/20000000000000 : ℝ)^3605
        have hw : |(138318799/250000000 : ℝ)|=(138318799/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s1_5 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5267418171/10000000000 : ℝ)*x 0 + (-788322657/5000000000 : ℝ)*x 1 + (2766376179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5267418171/10000000000 : ℝ)^4629 ≤ (8781074604791/20000000000000 : ℝ)^3605 := by
    have hnat : (5267418171 : ℕ)^4629*20000000000000^3605 ≤ 8781074604791^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267418171 10000000000 8781074604791 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (788322657/5000000000 : ℝ)^4629 ≤ (4664664447821/50000000000000 : ℝ)^3605 := by
    have hnat : (788322657 : ℕ)^4629*50000000000000^3605 ≤ 4664664447821^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      788322657 5000000000 4664664447821 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2766376179/5000000000 : ℝ)^4629 ≤ (5845662257803/12500000000000 : ℝ)^3605 := by
    have hnat : (2766376179 : ℕ)^4629*12500000000000^3605 ≤ 5845662257803^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2766376179 5000000000 5845662257803 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5267418171/10000000000 : ℝ), (-788322657/5000000000 : ℝ), (2766376179/5000000000 : ℝ)] ![(8781074604791/20000000000000 : ℝ), (4664664447821/50000000000000 : ℝ), (5845662257803/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5267418171/10000000000 : ℝ)|^4629 ≤ (8781074604791/20000000000000 : ℝ)^3605
        have hw : |(5267418171/10000000000 : ℝ)|=(5267418171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-788322657/5000000000 : ℝ)|^4629 ≤ (4664664447821/50000000000000 : ℝ)^3605
        have hw : |(-788322657/5000000000 : ℝ)|=(788322657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2766376179/5000000000 : ℝ)|^4629 ≤ (5845662257803/12500000000000 : ℝ)^3605
        have hw : |(2766376179/5000000000 : ℝ)|=(2766376179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s1_6 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2633708867/5000000000 : ℝ)*x 0 + (1106550503/2000000000 : ℝ)*x 1 + (-315329141/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2633708867/5000000000 : ℝ)^4629 ≤ (1372042760837/3125000000000 : ℝ)^3605 := by
    have hnat : (2633708867 : ℕ)^4629*3125000000000^3605 ≤ 1372042760837^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633708867 5000000000 1372042760837 3125000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106550503/2000000000 : ℝ)^4629 ≤ (23382649883201/50000000000000 : ℝ)^3605 := by
    have hnat : (1106550503 : ℕ)^4629*50000000000000^3605 ≤ 23382649883201^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106550503 2000000000 23382649883201 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315329141/2000000000 : ℝ)^4629 ≤ (4664665933227/50000000000000 : ℝ)^3605 := by
    have hnat : (315329141 : ℕ)^4629*50000000000000^3605 ≤ 4664665933227^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315329141 2000000000 4664665933227 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2633708867/5000000000 : ℝ), (1106550503/2000000000 : ℝ), (-315329141/2000000000 : ℝ)] ![(1372042760837/3125000000000 : ℝ), (23382649883201/50000000000000 : ℝ), (4664665933227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2633708867/5000000000 : ℝ)|^4629 ≤ (1372042760837/3125000000000 : ℝ)^3605
        have hw : |(2633708867/5000000000 : ℝ)|=(2633708867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106550503/2000000000 : ℝ)|^4629 ≤ (23382649883201/50000000000000 : ℝ)^3605
        have hw : |(1106550503/2000000000 : ℝ)|=(1106550503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315329141/2000000000 : ℝ)|^4629 ≤ (4664665933227/50000000000000 : ℝ)^3605
        have hw : |(-315329141/2000000000 : ℝ)|=(315329141/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s1_7 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4230425427/10000000000 : ℝ)*x 0 + (1182454533/2500000000 : ℝ)*x 1 + (377556513/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4230425427/10000000000 : ℝ)^4629 ≤ (33132824290673/100000000000000 : ℝ)^3605 := by
    have hnat : (4230425427 : ℕ)^4629*100000000000000^3605 ≤ 33132824290673^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230425427 10000000000 33132824290673 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1182454533/2500000000 : ℝ)^4629 ≤ (9559254777391/25000000000000 : ℝ)^3605 := by
    have hnat : (1182454533 : ℕ)^4629*25000000000000^3605 ≤ 9559254777391^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182454533 2500000000 9559254777391 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377556513/1000000000 : ℝ)^4629 ≤ (14315078293581/50000000000000 : ℝ)^3605 := by
    have hnat : (377556513 : ℕ)^4629*50000000000000^3605 ≤ 14315078293581^3605*1000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377556513 1000000000 14315078293581 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4230425427/10000000000 : ℝ), (1182454533/2500000000 : ℝ), (377556513/1000000000 : ℝ)] ![(33132824290673/100000000000000 : ℝ), (9559254777391/25000000000000 : ℝ), (14315078293581/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4230425427/10000000000 : ℝ)|^4629 ≤ (33132824290673/100000000000000 : ℝ)^3605
        have hw : |(4230425427/10000000000 : ℝ)|=(4230425427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1182454533/2500000000 : ℝ)|^4629 ≤ (9559254777391/25000000000000 : ℝ)^3605
        have hw : |(1182454533/2500000000 : ℝ)|=(1182454533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377556513/1000000000 : ℝ)|^4629 ≤ (14315078293581/50000000000000 : ℝ)^3605
        have hw : |(377556513/1000000000 : ℝ)|=(377556513/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1566_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24803/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (282/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (556/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24803/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24803/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3497/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24803/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24803/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3497/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24803/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24803/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3497/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3497/100000 : ℝ) ^ (4627/1024 : ℝ) ≤ (13139507201741/50000000000000000000 : ℝ) := by
    have hpowers : (3497/100000 : ℝ)^4627 ≤ (13139507201741/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3497 : ℕ)^4627*50000000000000000000^1024 ≤ 13139507201741^1024*100000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3497 100000 13139507201741 50000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3497/100000 : ℝ)) (X := (13139507201741/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24803/100000 : ℝ) ^ (4627/1024 : ℝ) ≤ (91834143308597417/50000000000000000000 : ℝ) := by
    have hpowers : (24803/100000 : ℝ)^4627 ≤ (91834143308597417/50000000000000000000 : ℝ)^1024 := by
      have hnat : (24803 : ℕ)^4627*50000000000000000000^1024 ≤ 91834143308597417^1024*100000^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24803 100000 91834143308597417 50000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24803/100000 : ℝ)) (X := (91834143308597417/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000013139507201741/25000000000000000000 : ℝ) ≤ (5000000581579971/5000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (25000013139507201741/25000000000000000000 : ℝ)^1024 ≤ (5000000581579971/5000000000000000 : ℝ)^4627 := by
      have hnat : (25000013139507201741 : ℕ)^1024*5000000000000000^4627 ≤ 5000000581579971^4627*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000013139507201741 25000000000000000000 5000000581579971 5000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000581579971/5000000000000000 : ℝ)) (X := (25000013139507201741/25000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25045923641407899579/25000000000000000000 : ℝ) ≤ (5002031217300653/5000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (25045923641407899579/25000000000000000000 : ℝ)^1024 ≤ (5002031217300653/5000000000000000 : ℝ)^4627 := by
      have hnat : (25045923641407899579 : ℕ)^1024*5000000000000000^4627 ≤ 5002031217300653^4627*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25045923641407899579 25000000000000000000 5002031217300653 5000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002031217300653/5000000000000000 : ℝ)) (X := (25045923641407899579/25000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25091834143308597417/25000000000000000000 : ℝ) ≤ (1000812370604267/1000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (25091834143308597417/25000000000000000000 : ℝ)^1024 ≤ (1000812370604267/1000000000000000 : ℝ)^4627 := by
      have hnat : (25091834143308597417 : ℕ)^1024*1000000000000000^4627 ≤ 1000812370604267^4627*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25091834143308597417 25000000000000000000 1000812370604267 1000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000812370604267/1000000000000000 : ℝ)) (X := (25091834143308597417/25000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13139507201741/50000000000000000000 : ℝ) ≤ ((53257905062456206109/53265000000000000000 : ℝ)+2*(1015317860341/532650000000000 : ℝ)*(3497/100000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (53257905062456206109/53265000000000000000 : ℝ)+2*(1015317860341/532650000000000 : ℝ)*(3497/100000 : ℝ)=(5000000581579971/5000000000000000 : ℝ) by norm_num, show 1+2*(13139507201741/50000000000000000000 : ℝ)=(25000013139507201741/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(91834143308597417/50000000000000000000 : ℝ)+(13139507201741/50000000000000000000 : ℝ) ≤ ((53257905062456206109/53265000000000000000 : ℝ)+(1015317860341/532650000000000 : ℝ)*((24803/100000 : ℝ)+(3497/100000 : ℝ)))^(4627/1024 : ℝ) := by
    rw [show (53257905062456206109/53265000000000000000 : ℝ)+(1015317860341/532650000000000 : ℝ)*((24803/100000 : ℝ)+(3497/100000 : ℝ))=(5002031217300653/5000000000000000 : ℝ) by norm_num, show 1+(91834143308597417/50000000000000000000 : ℝ)+(13139507201741/50000000000000000000 : ℝ)=(25045923641407899579/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(91834143308597417/50000000000000000000 : ℝ) ≤ ((53257905062456206109/53265000000000000000 : ℝ)+2*(1015317860341/532650000000000 : ℝ)*(24803/100000 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (53257905062456206109/53265000000000000000 : ℝ)+2*(1015317860341/532650000000000 : ℝ)*(24803/100000 : ℝ)=(1000812370604267/1000000000000000 : ℝ) by norm_num, show 1+2*(91834143308597417/50000000000000000000 : ℝ)=(25091834143308597417/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (53257905062456206109/53265000000000000000 : ℝ)*(X 1 0+X 2 0)+(1015317860341/532650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (3497/100000 : ℝ)) (hi := (24803/100000 : ℝ)) (c := (53257905062456206109/53265000000000000000 : ℝ)) (alpha := (1015317860341/532650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (53257905062456206109/53265000000000000000 : ℝ)*(X 0 1+X 2 1)+(1015317860341/532650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (3497/100000 : ℝ)) (hi := (24803/100000 : ℝ)) (c := (53257905062456206109/53265000000000000000 : ℝ)) (alpha := (1015317860341/532650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (53257905062456206109/53265000000000000000 : ℝ)*(X 0 2+X 1 2)+(1015317860341/532650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (3497/100000 : ℝ)) (hi := (24803/100000 : ℝ)) (c := (53257905062456206109/53265000000000000000 : ℝ)) (alpha := (1015317860341/532650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-353929473/2000000000 : ℝ)*X 0 0+(86517347/156250000 : ℝ)*X 0 1+(1280776369/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5377114329/10000000000 : ℝ)*X 1 0+(-1986292057/10000000000 : ℝ)*X 1 1+(5123105337/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2688557117/5000000000 : ℝ)*X 2 0+(512310579/1000000000 : ℝ)*X 2 1+(-198629159/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1057479301/2500000000 : ℝ)*X 0 0+(150612201/400000000 : ℝ)*X 0 1+(473992767/1000000000 : ℝ)*X 0 2+(1057479301/2500000000 : ℝ)*X 1 0+(150612201/400000000 : ℝ)*X 1 1+(473992767/1000000000 : ℝ)*X 1 2+(1057479301/2500000000 : ℝ)*X 2 0+(150612201/400000000 : ℝ)*X 2 1+(473992767/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-442465939/2500000000 : ℝ)*X 0 0+(512739999/1000000000 : ℝ)*X 0 1+(138318799/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5267418171/10000000000 : ℝ)*X 1 0+(-788322657/5000000000 : ℝ)*X 1 1+(2766376179/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2633708867/5000000000 : ℝ)*X 2 0+(1106550503/2000000000 : ℝ)*X 2 1+(-315329141/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4230425427/10000000000 : ℝ)*X 0 0+(1182454533/2500000000 : ℝ)*X 0 1+(377556513/1000000000 : ℝ)*X 0 2+(4230425427/10000000000 : ℝ)*X 1 0+(1182454533/2500000000 : ℝ)*X 1 1+(377556513/1000000000 : ℝ)*X 1 2+(4230425427/10000000000 : ℝ)*X 2 0+(1182454533/2500000000 : ℝ)*X 2 1+(377556513/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3365679228591289361423292699/443875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126788317/100000000000000 : ℝ)*(base1) + (897260521/50000000000000 : ℝ)*(base19) + (175184599/10000000000000 : ℝ)*(base23) + (36647939/50000000000000 : ℝ)*(upper3) + (2061667/625000000000 : ℝ)*(upper5) + (1720756811744511/100000000000000 : ℝ)*(major0) + (1720756811744511/100000000000000 : ℝ)*(major1) + (1720756811744511/100000000000000 : ℝ)*(major2) + (1207722041291183/50000000000000 : ℝ)*(sp0) + (603864832697519/25000000000000 : ℝ)*(sp1) + (301932421683141/12500000000000 : ℝ)*(sp2) + (1026045841758977/100000000000000 : ℝ)*(sp3) + (17169517069/100000000000000 : ℝ)*(sp4) + (3138440413/50000000000000 : ℝ)*(sp7) + (25651306135703/2500000000000 : ℝ)*(f.failure) + (1207730562655559/50000000000000 : ℝ)*(f.sum) + (14076264458223/8877500000000000000000000000 : ℝ)*base66 + (1224179747675660767/1775500000000000000000000000000000 : ℝ)*base68 + (8966983497466160767/1775500000000000000000000000000000 : ℝ)*base70 + (11730140150960160767/1775500000000000000000000000000000 : ℝ)*base72 + (1565905510541/17755000000000000000000000000 : ℝ)*base74 + (1054279821444160767/1775500000000000000000000000000000 : ℝ)*base76 + (483820949865839233/1775500000000000000000000000000000 : ℝ)*base77 + (15330650968066660767/1775500000000000000000000000000000 : ℝ)*base80 + (21688808941479/4438750000000000000000000000 : ℝ)*base82 + (1681053/250000000000000000000 : ℝ)*base90 + (1681053/250000000000000000000 : ℝ)*base92 + (1681053/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9411958527100969467723595101/887750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1898380623/100000000000000 : ℝ)*(base19) + (1731688961/100000000000000 : ℝ)*(base23) + (6014073/20000000000000 : ℝ)*(upper2) + (320395037/100000000000000 : ℝ)*(upper3) + (99860691/50000000000000 : ℝ)*(upper5) + (1757464825698437/100000000000000 : ℝ)*(major0) + (1757464825698437/100000000000000 : ℝ)*(major1) + (1757464825698437/100000000000000 : ℝ)*(major2) + (3055531821/20000000000000 : ℝ)*(sp1) + (448748229/3125000000000 : ℝ)*(sp2) + (616747202841787/25000000000000 : ℝ)*(sp4) + (123348581766371/5000000000000 : ℝ)*(sp5) + (2466972719734859/100000000000000 : ℝ)*(sp6) + (261985121657121/25000000000000 : ℝ)*(sp7) + (261985121657121/25000000000000 : ℝ)*(f.failure) + (616747202841787/25000000000000 : ℝ)*(f.sum) + (4212281158667/26632500000000000000000000000 : ℝ)*base65 + (6627221422213617211/1775500000000000000000000000000000 : ℝ)*base67 + (1433222385117617211/1775500000000000000000000000000000 : ℝ)*base69 + (6982984349526117211/1775500000000000000000000000000000 : ℝ)*base71 + (136518458503939/53265000000000000000000000000 : ℝ)*base73 + (4233914434910117211/1775500000000000000000000000000000 : ℝ)*base75 + (3820186961504617211/1775500000000000000000000000000000 : ℝ)*base77 + (2237189393346117211/1775500000000000000000000000000000 : ℝ)*base79 + (17519772795709/53265000000000000000000000000 : ℝ)*base81 + (814571/2500000000000000000000 : ℝ)*base90 + (814571/2500000000000000000000 : ℝ)*base92 + (814571/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1566_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24803/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3497/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (282/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (556/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1566_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1566_s2_0 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1788608153/10000000000 : ℝ)*x 0 + (1360616217/2500000000 : ℝ)*x 1 + (2602699903/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1788608153/10000000000 : ℝ)^4629 ≤ (548481781493/5000000000000 : ℝ)^3605 := by
    have hnat : (1788608153 : ℕ)^4629*5000000000000^3605 ≤ 548481781493^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788608153 10000000000 548481781493 5000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360616217/2500000000 : ℝ)^4629 ≤ (45787655071111/100000000000000 : ℝ)^3605 := by
    have hnat : (1360616217 : ℕ)^4629*100000000000000^3605 ≤ 45787655071111^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360616217 2500000000 45787655071111 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2602699903/5000000000 : ℝ)^4629 ≤ (5405338659917/12500000000000 : ℝ)^3605 := by
    have hnat : (2602699903 : ℕ)^4629*12500000000000^3605 ≤ 5405338659917^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2602699903 5000000000 5405338659917 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1788608153/10000000000 : ℝ), (1360616217/2500000000 : ℝ), (2602699903/5000000000 : ℝ)] ![(548481781493/5000000000000 : ℝ), (45787655071111/100000000000000 : ℝ), (5405338659917/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1788608153/10000000000 : ℝ)|^4629 ≤ (548481781493/5000000000000 : ℝ)^3605
        have hw : |(-1788608153/10000000000 : ℝ)|=(1788608153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360616217/2500000000 : ℝ)|^4629 ≤ (45787655071111/100000000000000 : ℝ)^3605
        have hw : |(1360616217/2500000000 : ℝ)|=(1360616217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2602699903/5000000000 : ℝ)|^4629 ≤ (5405338659917/12500000000000 : ℝ)^3605
        have hw : |(2602699903/5000000000 : ℝ)|=(2602699903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_1 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267634761/500000000 : ℝ)*x 0 + (-119393951/625000000 : ℝ)*x 1 + (104107991/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267634761/500000000 : ℝ)^4629 ≤ (44820175983091/100000000000000 : ℝ)^3605 := by
    have hnat : (267634761 : ℕ)^4629*100000000000000^3605 ≤ 44820175983091^3605*500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267634761 500000000 44820175983091 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119393951/625000000 : ℝ)^4629 ≤ (11937117449757/100000000000000 : ℝ)^3605 := by
    have hnat : (119393951 : ℕ)^4629*100000000000000^3605 ≤ 11937117449757^3605*625000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119393951 625000000 11937117449757 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104107991/200000000 : ℝ)^4629 ≤ (21621353274297/50000000000000 : ℝ)^3605 := by
    have hnat : (104107991 : ℕ)^4629*50000000000000^3605 ≤ 21621353274297^3605*200000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104107991 200000000 21621353274297 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267634761/500000000 : ℝ), (-119393951/625000000 : ℝ), (104107991/200000000 : ℝ)] ![(44820175983091/100000000000000 : ℝ), (11937117449757/100000000000000 : ℝ), (21621353274297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267634761/500000000 : ℝ)|^4629 ≤ (44820175983091/100000000000000 : ℝ)^3605
        have hw : |(267634761/500000000 : ℝ)|=(267634761/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-119393951/625000000 : ℝ)|^4629 ≤ (11937117449757/100000000000000 : ℝ)^3605
        have hw : |(-119393951/625000000 : ℝ)|=(119393951/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104107991/200000000 : ℝ)|^4629 ≤ (21621353274297/50000000000000 : ℝ)^3605
        have hw : |(104107991/200000000 : ℝ)|=(104107991/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_2 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352696397/10000000000 : ℝ)*x 0 + (5205399079/10000000000 : ℝ)*x 1 + (-382060453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352696397/10000000000 : ℝ)^4629 ≤ (11205047159503/25000000000000 : ℝ)^3605 := by
    have hnat : (5352696397 : ℕ)^4629*25000000000000^3605 ≤ 11205047159503^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352696397 10000000000 11205047159503 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205399079/10000000000 : ℝ)^4629 ≤ (5405337690557/12500000000000 : ℝ)^3605 := by
    have hnat : (5205399079 : ℕ)^4629*12500000000000^3605 ≤ 5405337690557^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205399079 10000000000 5405337690557 12500000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (382060453/2000000000 : ℝ)^4629 ≤ (5968554909571/50000000000000 : ℝ)^3605 := by
    have hnat : (382060453 : ℕ)^4629*50000000000000^3605 ≤ 5968554909571^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      382060453 2000000000 5968554909571 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352696397/10000000000 : ℝ), (5205399079/10000000000 : ℝ), (-382060453/2000000000 : ℝ)] ![(11205047159503/25000000000000 : ℝ), (5405337690557/12500000000000 : ℝ), (5968554909571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352696397/10000000000 : ℝ)|^4629 ≤ (11205047159503/25000000000000 : ℝ)^3605
        have hw : |(5352696397/10000000000 : ℝ)|=(5352696397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205399079/10000000000 : ℝ)|^4629 ≤ (5405337690557/12500000000000 : ℝ)^3605
        have hw : |(5205399079/10000000000 : ℝ)|=(5205399079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-382060453/2000000000 : ℝ)|^4629 ≤ (5968554909571/50000000000000 : ℝ)^3605
        have hw : |(-382060453/2000000000 : ℝ)|=(382060453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_3 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848729467/2000000000 : ℝ)*x 0 + (248253419/625000000 : ℝ)*x 1 + (4530140873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848729467/2000000000 : ℝ)^4629 ≤ (16632926143327/50000000000000 : ℝ)^3605 := by
    have hnat : (848729467 : ℕ)^4629*50000000000000^3605 ≤ 16632926143327^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848729467 2000000000 16632926143327 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (248253419/625000000 : ℝ)^4629 ≤ (15278669154427/50000000000000 : ℝ)^3605 := by
    have hnat : (248253419 : ℕ)^4629*50000000000000^3605 ≤ 15278669154427^3605*625000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      248253419 625000000 15278669154427 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4530140873/10000000000 : ℝ)^4629 ≤ (36176809396901/100000000000000 : ℝ)^3605 := by
    have hnat : (4530140873 : ℕ)^4629*100000000000000^3605 ≤ 36176809396901^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530140873 10000000000 36176809396901 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848729467/2000000000 : ℝ), (248253419/625000000 : ℝ), (4530140873/10000000000 : ℝ)] ![(16632926143327/50000000000000 : ℝ), (15278669154427/50000000000000 : ℝ), (36176809396901/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848729467/2000000000 : ℝ)|^4629 ≤ (16632926143327/50000000000000 : ℝ)^3605
        have hw : |(848729467/2000000000 : ℝ)|=(848729467/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(248253419/625000000 : ℝ)|^4629 ≤ (15278669154427/50000000000000 : ℝ)^3605
        have hw : |(248253419/625000000 : ℝ)|=(248253419/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4530140873/10000000000 : ℝ)|^4629 ≤ (36176809396901/100000000000000 : ℝ)^3605
        have hw : |(4530140873/10000000000 : ℝ)|=(4530140873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_4 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1788645547/10000000000 : ℝ)*x 0 + (2603408191/5000000000 : ℝ)*x 1 + (1360259683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1788645547/10000000000 : ℝ)^4629 ≤ (10969930114143/100000000000000 : ℝ)^3605 := by
    have hnat : (1788645547 : ℕ)^4629*100000000000000^3605 ≤ 10969930114143^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1788645547 10000000000 10969930114143 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2603408191/5000000000 : ℝ)^4629 ≤ (337951722067/781250000000 : ℝ)^3605 := by
    have hnat : (2603408191 : ℕ)^4629*781250000000^3605 ≤ 337951722067^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2603408191 5000000000 337951722067 781250000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360259683/2500000000 : ℝ)^4629 ≤ (22886124720631/50000000000000 : ℝ)^3605 := by
    have hnat : (1360259683 : ℕ)^4629*50000000000000^3605 ≤ 22886124720631^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360259683 2500000000 22886124720631 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1788645547/10000000000 : ℝ), (2603408191/5000000000 : ℝ), (1360259683/2500000000 : ℝ)] ![(10969930114143/100000000000000 : ℝ), (337951722067/781250000000 : ℝ), (22886124720631/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1788645547/10000000000 : ℝ)|^4629 ≤ (10969930114143/100000000000000 : ℝ)^3605
        have hw : |(-1788645547/10000000000 : ℝ)|=(1788645547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2603408191/5000000000 : ℝ)|^4629 ≤ (337951722067/781250000000 : ℝ)^3605
        have hw : |(2603408191/5000000000 : ℝ)|=(2603408191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360259683/2500000000 : ℝ)|^4629 ≤ (22886124720631/50000000000000 : ℝ)^3605
        have hw : |(1360259683/2500000000 : ℝ)|=(1360259683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_5 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289997451/10000000000 : ℝ)*x 0 + (-1674664521/10000000000 : ℝ)*x 1 + (1360259883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289997451/10000000000 : ℝ)^4629 ≤ (22073591976119/50000000000000 : ℝ)^3605 := by
    have hnat : (5289997451 : ℕ)^4629*50000000000000^3605 ≤ 22073591976119^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289997451 10000000000 22073591976119 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1674664521/10000000000 : ℝ)^4629 ≤ (2016111589747/20000000000000 : ℝ)^3605 := by
    have hnat : (1674664521 : ℕ)^4629*20000000000000^3605 ≤ 2016111589747^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1674664521 10000000000 2016111589747 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1360259883/2500000000 : ℝ)^4629 ≤ (22886129041413/50000000000000 : ℝ)^3605 := by
    have hnat : (1360259883 : ℕ)^4629*50000000000000^3605 ≤ 22886129041413^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360259883 2500000000 22886129041413 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289997451/10000000000 : ℝ), (-1674664521/10000000000 : ℝ), (1360259883/2500000000 : ℝ)] ![(22073591976119/50000000000000 : ℝ), (2016111589747/20000000000000 : ℝ), (22886129041413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289997451/10000000000 : ℝ)|^4629 ≤ (22073591976119/50000000000000 : ℝ)^3605
        have hw : |(5289997451/10000000000 : ℝ)|=(5289997451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1674664521/10000000000 : ℝ)|^4629 ≤ (2016111589747/20000000000000 : ℝ)^3605
        have hw : |(-1674664521/10000000000 : ℝ)|=(1674664521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1360259883/2500000000 : ℝ)|^4629 ≤ (22886129041413/50000000000000 : ℝ)^3605
        have hw : |(1360259883/2500000000 : ℝ)|=(1360259883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_6 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289997709/10000000000 : ℝ)*x 0 + (5441040571/10000000000 : ℝ)*x 1 + (-209332839/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289997709/10000000000 : ℝ)^4629 ≤ (22073593358473/50000000000000 : ℝ)^3605 := by
    have hnat : (5289997709 : ℕ)^4629*50000000000000^3605 ≤ 22073593358473^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289997709 10000000000 22073593358473 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441040571/10000000000 : ℝ)^4629 ≤ (45772269306057/100000000000000 : ℝ)^3605 := by
    have hnat : (5441040571 : ℕ)^4629*100000000000000^3605 ≤ 45772269306057^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441040571 10000000000 45772269306057 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209332839/1250000000 : ℝ)^4629 ≤ (5040271983241/50000000000000 : ℝ)^3605 := by
    have hnat : (209332839 : ℕ)^4629*50000000000000^3605 ≤ 5040271983241^3605*1250000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209332839 1250000000 5040271983241 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289997709/10000000000 : ℝ), (5441040571/10000000000 : ℝ), (-209332839/1250000000 : ℝ)] ![(22073593358473/50000000000000 : ℝ), (45772269306057/100000000000000 : ℝ), (5040271983241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289997709/10000000000 : ℝ)|^4629 ≤ (22073593358473/50000000000000 : ℝ)^3605
        have hw : |(5289997709/10000000000 : ℝ)|=(5289997709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441040571/10000000000 : ℝ)|^4629 ≤ (45772269306057/100000000000000 : ℝ)^3605
        have hw : |(5441040571/10000000000 : ℝ)|=(5441040571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-209332839/1250000000 : ℝ)|^4629 ≤ (5040271983241/50000000000000 : ℝ)^3605
        have hw : |(-209332839/1250000000 : ℝ)|=(209332839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_7 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4243744101/10000000000 : ℝ)*x 0 + (4526806963/10000000000 : ℝ)*x 1 + (3975416101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4243744101/10000000000 : ℝ)^4629 ≤ (33266826301277/100000000000000 : ℝ)^3605 := by
    have hnat : (4243744101 : ℕ)^4629*100000000000000^3605 ≤ 33266826301277^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243744101 10000000000 33266826301277 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4526806963/10000000000 : ℝ)^4629 ≤ (9035656623641/25000000000000 : ℝ)^3605 := by
    have hnat : (4526806963 : ℕ)^4629*25000000000000^3605 ≤ 9035656623641^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526806963 10000000000 9035656623641 25000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3975416101/10000000000 : ℝ)^4629 ≤ (30590547187067/100000000000000 : ℝ)^3605 := by
    have hnat : (3975416101 : ℕ)^4629*100000000000000^3605 ≤ 30590547187067^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3975416101 10000000000 30590547187067 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4243744101/10000000000 : ℝ), (4526806963/10000000000 : ℝ), (3975416101/10000000000 : ℝ)] ![(33266826301277/100000000000000 : ℝ), (9035656623641/25000000000000 : ℝ), (30590547187067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4243744101/10000000000 : ℝ)|^4629 ≤ (33266826301277/100000000000000 : ℝ)^3605
        have hw : |(4243744101/10000000000 : ℝ)|=(4243744101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4526806963/10000000000 : ℝ)|^4629 ≤ (9035656623641/25000000000000 : ℝ)^3605
        have hw : |(4526806963/10000000000 : ℝ)|=(4526806963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3975416101/10000000000 : ℝ)|^4629 ≤ (30590547187067/100000000000000 : ℝ)^3605
        have hw : |(3975416101/10000000000 : ℝ)|=(3975416101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_8 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-5674761/10000000000 : ℝ)*x 0 + (5828073487/10000000000 : ℝ)*x 1 + (2914225857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5674761/10000000000 : ℝ)^4629 ≤ (6790575923/100000000000000 : ℝ)^3605 := by
    have hnat : (5674761 : ℕ)^4629*100000000000000^3605 ≤ 6790575923^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5674761 10000000000 6790575923 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5828073487/10000000000 : ℝ)^4629 ≤ (9998904325283/20000000000000 : ℝ)^3605 := by
    have hnat : (5828073487 : ℕ)^4629*20000000000000^3605 ≤ 9998904325283^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5828073487 10000000000 9998904325283 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2914225857/5000000000 : ℝ)^4629 ≤ (24999343892707/50000000000000 : ℝ)^3605 := by
    have hnat : (2914225857 : ℕ)^4629*50000000000000^3605 ≤ 24999343892707^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914225857 5000000000 24999343892707 50000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5674761/10000000000 : ℝ), (5828073487/10000000000 : ℝ), (2914225857/5000000000 : ℝ)] ![(6790575923/100000000000000 : ℝ), (9998904325283/20000000000000 : ℝ), (24999343892707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5674761/10000000000 : ℝ)|^4629 ≤ (6790575923/100000000000000 : ℝ)^3605
        have hw : |(-5674761/10000000000 : ℝ)|=(5674761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5828073487/10000000000 : ℝ)|^4629 ≤ (9998904325283/20000000000000 : ℝ)^3605
        have hw : |(5828073487/10000000000 : ℝ)|=(5828073487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2914225857/5000000000 : ℝ)|^4629 ≤ (24999343892707/50000000000000 : ℝ)^3605
        have hw : |(2914225857/5000000000 : ℝ)|=(2914225857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_9 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (257054823/2500000000 : ℝ)*x 0 + (-4246479819/10000000000 : ℝ)*x 1 + (6832374693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257054823/2500000000 : ℝ)^4629 ≤ (5388510994647/100000000000000 : ℝ)^3605 := by
    have hnat : (257054823 : ℕ)^4629*100000000000000^3605 ≤ 5388510994647^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257054823 2500000000 5388510994647 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246479819/10000000000 : ℝ)^4629 ≤ (33294365745829/100000000000000 : ℝ)^3605 := by
    have hnat : (4246479819 : ℕ)^4629*100000000000000^3605 ≤ 33294365745829^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246479819 10000000000 33294365745829 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6832374693/10000000000 : ℝ)^4629 ≤ (12263424648211/20000000000000 : ℝ)^3605 := by
    have hnat : (6832374693 : ℕ)^4629*20000000000000^3605 ≤ 12263424648211^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6832374693 10000000000 12263424648211 20000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257054823/2500000000 : ℝ), (-4246479819/10000000000 : ℝ), (6832374693/10000000000 : ℝ)] ![(5388510994647/100000000000000 : ℝ), (33294365745829/100000000000000 : ℝ), (12263424648211/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257054823/2500000000 : ℝ)|^4629 ≤ (5388510994647/100000000000000 : ℝ)^3605
        have hw : |(257054823/2500000000 : ℝ)|=(257054823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4246479819/10000000000 : ℝ)|^4629 ≤ (33294365745829/100000000000000 : ℝ)^3605
        have hw : |(-4246479819/10000000000 : ℝ)|=(4246479819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6832374693/10000000000 : ℝ)|^4629 ≤ (12263424648211/20000000000000 : ℝ)^3605
        have hw : |(6832374693/10000000000 : ℝ)|=(6832374693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_10 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1027029153/10000000000 : ℝ)*x 0 + (136590017/200000000 : ℝ)*x 1 + (-850112789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027029153/10000000000 : ℝ)^4629 ≤ (5380503600533/100000000000000 : ℝ)^3605 := by
    have hnat : (1027029153 : ℕ)^4629*100000000000000^3605 ≤ 5380503600533^3605*10000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027029153 10000000000 5380503600533 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136590017/200000000 : ℝ)^4629 ≤ (61284007910183/100000000000000 : ℝ)^3605 := by
    have hnat : (136590017 : ℕ)^4629*100000000000000^3605 ≤ 61284007910183^3605*200000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136590017 200000000 61284007910183 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (850112789/2000000000 : ℝ)^4629 ≤ (33335488484529/100000000000000 : ℝ)^3605 := by
    have hnat : (850112789 : ℕ)^4629*100000000000000^3605 ≤ 33335488484529^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850112789 2000000000 33335488484529 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1027029153/10000000000 : ℝ), (136590017/200000000 : ℝ), (-850112789/2000000000 : ℝ)] ![(5380503600533/100000000000000 : ℝ), (61284007910183/100000000000000 : ℝ), (33335488484529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1027029153/10000000000 : ℝ)|^4629 ≤ (5380503600533/100000000000000 : ℝ)^3605
        have hw : |(1027029153/10000000000 : ℝ)|=(1027029153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136590017/200000000 : ℝ)|^4629 ≤ (61284007910183/100000000000000 : ℝ)^3605
        have hw : |(136590017/200000000 : ℝ)|=(136590017/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-850112789/2000000000 : ℝ)|^4629 ≤ (33335488484529/100000000000000 : ℝ)^3605
        have hw : |(-850112789/2000000000 : ℝ)|=(850112789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1566_s2_11 (p : ℝ) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (392339829/2500000000 : ℝ)*x 0 + (2700737583/5000000000 : ℝ)*x 1 + (1080950627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (392339829/2500000000 : ℝ)^4629 ≤ (927400638113/10000000000000 : ℝ)^3605 := by
    have hnat : (392339829 : ℕ)^4629*10000000000000^3605 ≤ 927400638113^3605*2500000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392339829 2500000000 927400638113 10000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700737583/5000000000 : ℝ)^4629 ≤ (45345327705991/100000000000000 : ℝ)^3605 := by
    have hnat : (2700737583 : ℕ)^4629*100000000000000^3605 ≤ 45345327705991^3605*5000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700737583 5000000000 45345327705991 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080950627/2000000000 : ℝ)^4629 ≤ (45380665899111/100000000000000 : ℝ)^3605 := by
    have hnat : (1080950627 : ℕ)^4629*100000000000000^3605 ≤ 45380665899111^3605*2000000000^4629 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080950627 2000000000 45380665899111 100000000000000 4629 3605 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4629/1024 : ℝ)) 4629 3605 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(392339829/2500000000 : ℝ), (2700737583/5000000000 : ℝ), (1080950627/2000000000 : ℝ)] ![(927400638113/10000000000000 : ℝ), (45345327705991/100000000000000 : ℝ), (45380665899111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(392339829/2500000000 : ℝ)|^4629 ≤ (927400638113/10000000000000 : ℝ)^3605
        have hw : |(392339829/2500000000 : ℝ)|=(392339829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2700737583/5000000000 : ℝ)|^4629 ≤ (45345327705991/100000000000000 : ℝ)^3605
        have hw : |(2700737583/5000000000 : ℝ)|=(2700737583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080950627/2000000000 : ℝ)|^4629 ≤ (45380665899111/100000000000000 : ℝ)^3605
        have hw : |(1080950627/2000000000 : ℝ)|=(1080950627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1566_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (556/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (282/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (10797/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7911/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (556/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (282/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (556/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (282/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (556/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (282/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (556/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (282/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (556/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (282/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (556/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (282/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (282/3125 : ℝ) ^ (4627/1024 : ℝ) ≤ (190508188032037/10000000000000000000 : ℝ) := by
    have hpowers : (282/3125 : ℝ)^4627 ≤ (190508188032037/10000000000000000000 : ℝ)^1024 := by
      have hnat : (282 : ℕ)^4627*10000000000000000000^1024 ≤ 190508188032037^1024*3125^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        282 3125 190508188032037 10000000000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (282/3125 : ℝ)) (X := (190508188032037/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (556/3125 : ℝ) ^ (4627/1024 : ℝ) ≤ (639616480704713/1562500000000000000 : ℝ) := by
    have hpowers : (556/3125 : ℝ)^4627 ≤ (639616480704713/1562500000000000000 : ℝ)^1024 := by
      have hnat : (556 : ℕ)^4627*1562500000000000000^1024 ≤ 639616480704713^1024*3125^4627 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        556 3125 639616480704713 1562500000000000000 4627 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (556/3125 : ℝ)) (X := (639616480704713/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000190508188032037/5000000000000000000 : ℝ) ≤ (10000084321370501/10000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (5000190508188032037/5000000000000000000 : ℝ)^1024 ≤ (10000084321370501/10000000000000000 : ℝ)^4627 := by
      have hnat : (5000190508188032037 : ℕ)^1024*10000000000000000^4627 ≤ 10000084321370501^4627*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000190508188032037 5000000000000000000 10000084321370501 10000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084321370501/10000000000000000 : ℝ)) (X := (5000190508188032037/5000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021420268322711001/50000000000000000000 : ℝ) ≤ (10000947944546999/10000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (50021420268322711001/50000000000000000000 : ℝ)^1024 ≤ (10000947944546999/10000000000000000 : ℝ)^4627 := by
      have hnat : (50021420268322711001 : ℕ)^1024*10000000000000000^4627 ≤ 10000947944546999^4627*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021420268322711001 50000000000000000000 10000947944546999 10000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000947944546999/10000000000000000 : ℝ)) (X := (50021420268322711001/50000000000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781889616480704713/781250000000000000 : ℝ) ≤ (10001811567723497/10000000000000000 : ℝ) ^ (4627/1024 : ℝ) := by
    have hpowers : (781889616480704713/781250000000000000 : ℝ)^1024 ≤ (10001811567723497/10000000000000000 : ℝ)^4627 := by
      have hnat : (781889616480704713 : ℕ)^1024*10000000000000000^4627 ≤ 10001811567723497^4627*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781889616480704713 781250000000000000 10001811567723497 10000000000000000 1024 4627 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001811567723497/10000000000000000 : ℝ)) (X := (781889616480704713/781250000000000000 : ℝ)) (by norm_num) 4627 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(190508188032037/10000000000000000000 : ℝ) ≤ ((1369768010291986201/1370000000000000000 : ℝ)+2*(431811588249/438400000000000 : ℝ)*(282/3125 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (1369768010291986201/1370000000000000000 : ℝ)+2*(431811588249/438400000000000 : ℝ)*(282/3125 : ℝ)=(10000084321370501/10000000000000000 : ℝ) by norm_num, show 1+2*(190508188032037/10000000000000000000 : ℝ)=(5000190508188032037/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(639616480704713/1562500000000000000 : ℝ)+(190508188032037/10000000000000000000 : ℝ) ≤ ((1369768010291986201/1370000000000000000 : ℝ)+(431811588249/438400000000000 : ℝ)*((556/3125 : ℝ)+(282/3125 : ℝ)))^(4627/1024 : ℝ) := by
    rw [show (1369768010291986201/1370000000000000000 : ℝ)+(431811588249/438400000000000 : ℝ)*((556/3125 : ℝ)+(282/3125 : ℝ))=(10000947944546999/10000000000000000 : ℝ) by norm_num, show 1+(639616480704713/1562500000000000000 : ℝ)+(190508188032037/10000000000000000000 : ℝ)=(50021420268322711001/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(639616480704713/1562500000000000000 : ℝ) ≤ ((1369768010291986201/1370000000000000000 : ℝ)+2*(431811588249/438400000000000 : ℝ)*(556/3125 : ℝ))^(4627/1024 : ℝ) := by
    rw [show (1369768010291986201/1370000000000000000 : ℝ)+2*(431811588249/438400000000000 : ℝ)*(556/3125 : ℝ)=(10001811567723497/10000000000000000 : ℝ) by norm_num, show 1+2*(639616480704713/1562500000000000000 : ℝ)=(781889616480704713/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1369768010291986201/1370000000000000000 : ℝ)*(X 1 0+X 2 0)+(431811588249/438400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (282/3125 : ℝ)) (hi := (556/3125 : ℝ)) (c := (1369768010291986201/1370000000000000000 : ℝ)) (alpha := (431811588249/438400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1369768010291986201/1370000000000000000 : ℝ)*(X 0 1+X 2 1)+(431811588249/438400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (282/3125 : ℝ)) (hi := (556/3125 : ℝ)) (c := (1369768010291986201/1370000000000000000 : ℝ)) (alpha := (431811588249/438400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1369768010291986201/1370000000000000000 : ℝ)*(X 0 2+X 1 2)+(431811588249/438400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4627/1024 : ℝ)) (lo := (282/3125 : ℝ)) (hi := (556/3125 : ℝ)) (c := (1369768010291986201/1370000000000000000 : ℝ)) (alpha := (431811588249/438400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1788608153/10000000000 : ℝ)*X 0 0+(1360616217/2500000000 : ℝ)*X 0 1+(2602699903/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267634761/500000000 : ℝ)*X 1 0+(-119393951/625000000 : ℝ)*X 1 1+(104107991/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352696397/10000000000 : ℝ)*X 2 0+(5205399079/10000000000 : ℝ)*X 2 1+(-382060453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((848729467/2000000000 : ℝ)*X 0 0+(248253419/625000000 : ℝ)*X 0 1+(4530140873/10000000000 : ℝ)*X 0 2+(848729467/2000000000 : ℝ)*X 1 0+(248253419/625000000 : ℝ)*X 1 1+(4530140873/10000000000 : ℝ)*X 1 2+(848729467/2000000000 : ℝ)*X 2 0+(248253419/625000000 : ℝ)*X 2 1+(4530140873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1788645547/10000000000 : ℝ)*X 0 0+(2603408191/5000000000 : ℝ)*X 0 1+(1360259683/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289997451/10000000000 : ℝ)*X 1 0+(-1674664521/10000000000 : ℝ)*X 1 1+(1360259883/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5289997709/10000000000 : ℝ)*X 2 0+(5441040571/10000000000 : ℝ)*X 2 1+(-209332839/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4243744101/10000000000 : ℝ)*X 0 0+(4526806963/10000000000 : ℝ)*X 0 1+(3975416101/10000000000 : ℝ)*X 0 2+(4243744101/10000000000 : ℝ)*X 1 0+(4526806963/10000000000 : ℝ)*X 1 1+(3975416101/10000000000 : ℝ)*X 1 2+(4243744101/10000000000 : ℝ)*X 2 0+(4526806963/10000000000 : ℝ)*X 2 1+(3975416101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-5674761/10000000000 : ℝ)*X 0 0+(5828073487/10000000000 : ℝ)*X 0 1+(2914225857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((257054823/2500000000 : ℝ)*X 1 0+(-4246479819/10000000000 : ℝ)*X 1 1+(6832374693/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1027029153/10000000000 : ℝ)*X 2 0+(136590017/200000000 : ℝ)*X 2 1+(-850112789/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((392339829/2500000000 : ℝ)*X 0 0+(2700737583/5000000000 : ℝ)*X 0 1+(1080950627/2000000000 : ℝ)*X 0 2+(392339829/2500000000 : ℝ)*X 1 0+(2700737583/5000000000 : ℝ)*X 1 1+(1080950627/2000000000 : ℝ)*X 1 2+(392339829/2500000000 : ℝ)*X 2 0+(2700737583/5000000000 : ℝ)*X 2 1+(1080950627/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1566_s2_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (110531039027972090172400869/17125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (751263730251023/25000000000000 : ℝ)*(major0) + (751263730251023/25000000000000 : ℝ)*(major1) + (751263730251023/25000000000000 : ℝ)*(major2) + (2109124267533569/50000000000000 : ℝ)*(sp0) + (131819819381947/3125000000000 : ℝ)*(sp1) + (843647105101967/20000000000000 : ℝ)*(sp2) + (1791844740991741/100000000000000 : ℝ)*(sp3) + (2720297123/12500000000000 : ℝ)*(sp5) + (4818351501/25000000000000 : ℝ)*(sp6) + (801692313/10000000000000 : ℝ)*(sp7) + (2009301349/25000000000000 : ℝ)*(sp8) + (589673247/100000000000000 : ℝ)*(sp9) + (221669587/12500000000000 : ℝ)*(sp10) + (296675199/100000000000000 : ℝ)*(sp11) + (179185305459007/10000000000000 : ℝ)*(f.failure) + (843651314454507/20000000000000 : ℝ)*(f.sum) + (2249058080193/5480000000000000000000000000 : ℝ)*base66 + (71757686374952749/17125000000000000000000000000000 : ℝ)*base67 + (25460876745952749/17125000000000000000000000000000 : ℝ)*base69 + (192987116160172251/17125000000000000000000000000000 : ℝ)*base72 + (18652146965567/5480000000000000000000000000 : ℝ)*base73 + (6837025443922251/17125000000000000000000000000000 : ℝ)*base76 + (40201839691047251/17125000000000000000000000000000 : ℝ)*base78 + (19542165522672251/17125000000000000000000000000000 : ℝ)*base80 + (15956125182127/5480000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (4936843/1000000000000000000000 : ℝ)*base89 + (4936843/1000000000000000000000 : ℝ)*base91 + (4936843/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36399629626695344495008059/17125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20534451/12500000000000 : ℝ)*(base8) + (340350003/50000000000000 : ℝ)*(base15) + (111516939/100000000000000 : ℝ)*(base29) + (9551049/50000000000000 : ℝ)*(lower2) + (677249/2000000000000 : ℝ)*(lower4) + (76038009850367/2500000000000 : ℝ)*(major0) + (3041520505531619/100000000000000 : ℝ)*(major1) + (3041520505531619/100000000000000 : ℝ)*(major2) + (15606217/50000000000 : ℝ)*(sp2) + (1299013843/100000000000000 : ℝ)*(sp3) + (4269444035876471/100000000000000 : ℝ)*(sp4) + (4269443407935133/100000000000000 : ℝ)*(sp5) + (4269412876201139/100000000000000 : ℝ)*(sp6) + (1813595441046451/100000000000000 : ℝ)*(sp7) + (906798370030147/50000000000000 : ℝ)*(f.failure) + (2134722100076039/50000000000000 : ℝ)*(f.sum) + (71861118872651/21920000000000000000000000000 : ℝ)*base65 + (319432126943361897/68500000000000000000000000000000 : ℝ)*base67 + (366626328425861897/68500000000000000000000000000000 : ℝ)*base69 + (74497051452606989/27400000000000000000000000000000 : ℝ)*base72 + (59606759488829/43840000000000000000000000000 : ℝ)*base74 + (1398625795388064419/137000000000000000000000000000000 : ℝ)*base75 + (128533042184193011/27400000000000000000000000000000 : ℝ)*base77 + (645768063992064419/137000000000000000000000000000000 : ℝ)*base79 + (55903572635971/43840000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (29332703/5000000000000000000000 : ℝ)*base89 + (29332703/5000000000000000000000 : ℝ)*base91 + (29332703/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1566_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (556/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (282/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7911/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1566_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1566_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7911/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1566_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1566_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1566_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4627/1024 : ℝ) ≤ p) (hpb : p ≤ (4629/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167706549/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10797/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7911/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1566_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
