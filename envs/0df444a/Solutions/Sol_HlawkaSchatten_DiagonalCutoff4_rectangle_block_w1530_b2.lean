-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1530_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:04:54.574566+00:00
-- url     : https://prove2.me/submissions/0fbca78c-d01d-46c7-954b-433495576139

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
theorem support_rectangle_w1530_s6_0 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1841751219/10000000000 : ℝ)*x 0 + (678862357/1250000000 : ℝ)*x 1 + (2609248353/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1841751219/10000000000 : ℝ)^4557 ≤ (11278893367481/100000000000000 : ℝ)^3533 := by
    have hnat : (1841751219 : ℕ)^4557*100000000000000^3533 ≤ 11278893367481^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1841751219 10000000000 11278893367481 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678862357/1250000000 : ℝ)^4557 ≤ (1820066591413/4000000000000 : ℝ)^3533 := by
    have hnat : (678862357 : ℕ)^4557*4000000000000^3533 ≤ 1820066591413^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678862357 1250000000 1820066591413 4000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609248353/5000000000 : ℝ)^4557 ≤ (8643888365171/20000000000000 : ℝ)^3533 := by
    have hnat : (2609248353 : ℕ)^4557*20000000000000^3533 ≤ 8643888365171^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609248353 5000000000 8643888365171 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1841751219/10000000000 : ℝ), (678862357/1250000000 : ℝ), (2609248353/5000000000 : ℝ)] ![(11278893367481/100000000000000 : ℝ), (1820066591413/4000000000000 : ℝ), (8643888365171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1841751219/10000000000 : ℝ)|^4557 ≤ (11278893367481/100000000000000 : ℝ)^3533
        have hw : |(-1841751219/10000000000 : ℝ)|=(1841751219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678862357/1250000000 : ℝ)|^4557 ≤ (1820066591413/4000000000000 : ℝ)^3533
        have hw : |(678862357/1250000000 : ℝ)|=(678862357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609248353/5000000000 : ℝ)|^4557 ≤ (8643888365171/20000000000000 : ℝ)^3533
        have hw : |(2609248353/5000000000 : ℝ)|=(2609248353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s6_1 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675285411/5000000000 : ℝ)*x 0 + (-975247187/5000000000 : ℝ)*x 1 + (2609248359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675285411/5000000000 : ℝ)^4557 ≤ (44635455353731/100000000000000 : ℝ)^3533 := by
    have hnat : (2675285411 : ℕ)^4557*100000000000000^3533 ≤ 44635455353731^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675285411 5000000000 44635455353731 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (975247187/5000000000 : ℝ)^4557 ≤ (1518137834541/12500000000000 : ℝ)^3533 := by
    have hnat : (975247187 : ℕ)^4557*12500000000000^3533 ≤ 1518137834541^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      975247187 5000000000 1518137834541 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609248359/5000000000 : ℝ)^4557 ≤ (10804860488511/25000000000000 : ℝ)^3533 := by
    have hnat : (2609248359 : ℕ)^4557*25000000000000^3533 ≤ 10804860488511^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609248359 5000000000 10804860488511 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675285411/5000000000 : ℝ), (-975247187/5000000000 : ℝ), (2609248359/5000000000 : ℝ)] ![(44635455353731/100000000000000 : ℝ), (1518137834541/12500000000000 : ℝ), (10804860488511/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675285411/5000000000 : ℝ)|^4557 ≤ (44635455353731/100000000000000 : ℝ)^3533
        have hw : |(2675285411/5000000000 : ℝ)|=(2675285411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-975247187/5000000000 : ℝ)|^4557 ≤ (1518137834541/12500000000000 : ℝ)^3533
        have hw : |(-975247187/5000000000 : ℝ)|=(975247187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609248359/5000000000 : ℝ)|^4557 ≤ (10804860488511/25000000000000 : ℝ)^3533
        have hw : |(2609248359/5000000000 : ℝ)|=(2609248359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s6_2 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350570829/10000000000 : ℝ)*x 0 + (2609248353/5000000000 : ℝ)*x 1 + (-1950494381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350570829/10000000000 : ℝ)^4557 ≤ (44635455429051/100000000000000 : ℝ)^3533 := by
    have hnat : (5350570829 : ℕ)^4557*100000000000000^3533 ≤ 44635455429051^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350570829 10000000000 44635455429051 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609248353/5000000000 : ℝ)^4557 ≤ (8643888365171/20000000000000 : ℝ)^3533 := by
    have hnat : (2609248353 : ℕ)^4557*20000000000000^3533 ≤ 8643888365171^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609248353 5000000000 8643888365171 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1950494381/10000000000 : ℝ)^4557 ≤ (3036275683137/25000000000000 : ℝ)^3533 := by
    have hnat : (1950494381 : ℕ)^4557*25000000000000^3533 ≤ 3036275683137^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1950494381 10000000000 3036275683137 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350570829/10000000000 : ℝ), (2609248353/5000000000 : ℝ), (-1950494381/10000000000 : ℝ)] ![(44635455429051/100000000000000 : ℝ), (8643888365171/20000000000000 : ℝ), (3036275683137/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350570829/10000000000 : ℝ)|^4557 ≤ (44635455429051/100000000000000 : ℝ)^3533
        have hw : |(5350570829/10000000000 : ℝ)|=(5350570829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609248353/5000000000 : ℝ)|^4557 ≤ (8643888365171/20000000000000 : ℝ)^3533
        have hw : |(2609248353/5000000000 : ℝ)|=(2609248353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1950494381/10000000000 : ℝ)|^4557 ≤ (3036275683137/25000000000000 : ℝ)^3533
        have hw : |(-1950494381/10000000000 : ℝ)|=(1950494381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s6_3 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4261462809/10000000000 : ℝ)*x 0 + (4023422723/10000000000 : ℝ)*x 1 + (2255588983/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4261462809/10000000000 : ℝ)^4557 ≤ (16640274882699/50000000000000 : ℝ)^3533 := by
    have hnat : (4261462809 : ℕ)^4557*50000000000000^3533 ≤ 16640274882699^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261462809 10000000000 16640274882699 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023422723/10000000000 : ℝ)^4557 ≤ (15451199652143/50000000000000 : ℝ)^3533 := by
    have hnat : (4023422723 : ℕ)^4557*50000000000000^3533 ≤ 15451199652143^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023422723 10000000000 15451199652143 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2255588983/5000000000 : ℝ)^4557 ≤ (4477131364837/12500000000000 : ℝ)^3533 := by
    have hnat : (2255588983 : ℕ)^4557*12500000000000^3533 ≤ 4477131364837^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255588983 5000000000 4477131364837 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4261462809/10000000000 : ℝ), (4023422723/10000000000 : ℝ), (2255588983/5000000000 : ℝ)] ![(16640274882699/50000000000000 : ℝ), (15451199652143/50000000000000 : ℝ), (4477131364837/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4261462809/10000000000 : ℝ)|^4557 ≤ (16640274882699/50000000000000 : ℝ)^3533
        have hw : |(4261462809/10000000000 : ℝ)|=(4261462809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023422723/10000000000 : ℝ)|^4557 ≤ (15451199652143/50000000000000 : ℝ)^3533
        have hw : |(4023422723/10000000000 : ℝ)|=(4023422723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2255588983/5000000000 : ℝ)|^4557 ≤ (4477131364837/12500000000000 : ℝ)^3533
        have hw : |(2255588983/5000000000 : ℝ)|=(2255588983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s6_4 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-92088999/500000000 : ℝ)*x 0 + (2609797091/5000000000 : ℝ)*x 1 + (542979291/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92088999/500000000 : ℝ)^4557 ≤ (11279120550507/100000000000000 : ℝ)^3533 := by
    have hnat : (92088999 : ℕ)^4557*100000000000000^3533 ≤ 11279120550507^3533*500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92088999 500000000 11279120550507 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609797091/5000000000 : ℝ)^4557 ≤ (8646233173747/20000000000000 : ℝ)^3533 := by
    have hnat : (2609797091 : ℕ)^4557*20000000000000^3533 ≤ 8646233173747^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609797091 5000000000 8646233173747 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542979291/1000000000 : ℝ)^4557 ≤ (45489713570089/100000000000000 : ℝ)^3533 := by
    have hnat : (542979291 : ℕ)^4557*100000000000000^3533 ≤ 45489713570089^3533*1000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542979291 1000000000 45489713570089 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92088999/500000000 : ℝ), (2609797091/5000000000 : ℝ), (542979291/1000000000 : ℝ)] ![(11279120550507/100000000000000 : ℝ), (8646233173747/20000000000000 : ℝ), (45489713570089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92088999/500000000 : ℝ)|^4557 ≤ (11279120550507/100000000000000 : ℝ)^3533
        have hw : |(-92088999/500000000 : ℝ)|=(92088999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609797091/5000000000 : ℝ)|^4557 ≤ (8646233173747/20000000000000 : ℝ)^3533
        have hw : |(2609797091/5000000000 : ℝ)|=(2609797091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542979291/1000000000 : ℝ)|^4557 ≤ (45489713570089/100000000000000 : ℝ)^3533
        have hw : |(542979291/1000000000 : ℝ)|=(542979291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_s6_5 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1065382089/2500000000 : ℝ)*x 0 + (2254328799/5000000000 : ℝ)*x 1 + (4025960989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065382089/2500000000 : ℝ)^4557 ≤ (3328121003449/10000000000000 : ℝ)^3533 := by
    have hnat : (1065382089 : ℕ)^4557*10000000000000^3533 ≤ 3328121003449^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065382089 2500000000 3328121003449 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2254328799/5000000000 : ℝ)^4557 ≤ (894781058567/2500000000000 : ℝ)^3533 := by
    have hnat : (2254328799 : ℕ)^4557*2500000000000^3533 ≤ 894781058567^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2254328799 5000000000 894781058567 2500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4025960989/10000000000 : ℝ)^4557 ≤ (30927547611499/100000000000000 : ℝ)^3533 := by
    have hnat : (4025960989 : ℕ)^4557*100000000000000^3533 ≤ 30927547611499^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4025960989 10000000000 30927547611499 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1065382089/2500000000 : ℝ), (2254328799/5000000000 : ℝ), (4025960989/10000000000 : ℝ)] ![(3328121003449/10000000000000 : ℝ), (894781058567/2500000000000 : ℝ), (30927547611499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1065382089/2500000000 : ℝ)|^4557 ≤ (3328121003449/10000000000000 : ℝ)^3533
        have hw : |(1065382089/2500000000 : ℝ)|=(1065382089/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2254328799/5000000000 : ℝ)|^4557 ≤ (894781058567/2500000000000 : ℝ)^3533
        have hw : |(2254328799/5000000000 : ℝ)|=(2254328799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4025960989/10000000000 : ℝ)|^4557 ≤ (30927547611499/100000000000000 : ℝ)^3533
        have hw : |(4025960989/10000000000 : ℝ)|=(4025960989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1530_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1373/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10983/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10983/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10983/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10983/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10983/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10983/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10983/100000 : ℝ) ^ (4555/1024 : ℝ) ≤ (2703115569534599/50000000000000000000 : ℝ) := by
    have hpowers : (10983/100000 : ℝ)^4555 ≤ (2703115569534599/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10983 : ℕ)^4555*50000000000000000000^1024 ≤ 2703115569534599^1024*100000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10983 100000 2703115569534599 50000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10983/100000 : ℝ)) (X := (2703115569534599/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4555/1024 : ℝ) ≤ (24911742563996003/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4555 ≤ (24911742563996003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4555*100000000000000000000^1024 ≤ 24911742563996003^1024*25000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 24911742563996003 100000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (24911742563996003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002703115569534599/25000000000000000000 : ℝ) ≤ (5000121531255667/5000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (25002703115569534599/25000000000000000000 : ℝ)^1024 ≤ (5000121531255667/5000000000000000 : ℝ)^4555 := by
      have hnat : (25002703115569534599 : ℕ)^1024*5000000000000000^4555 ≤ 5000121531255667^4555*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002703115569534599 25000000000000000000 5000121531255667 5000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000121531255667/5000000000000000 : ℝ)) (X := (25002703115569534599/25000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100030317973703065201/100000000000000000000 : ℝ) ≤ (625042593245771/625000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (100030317973703065201/100000000000000000000 : ℝ)^1024 ≤ (625042593245771/625000000000000 : ℝ)^4555 := by
      have hnat : (100030317973703065201 : ℕ)^1024*625000000000000^4555 ≤ 625042593245771^4555*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100030317973703065201 100000000000000000000 625042593245771 625000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625042593245771/625000000000000 : ℝ)) (X := (100030317973703065201/100000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024911742563996003/50000000000000000000 : ℝ) ≤ (5000559960676669/5000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (50024911742563996003/50000000000000000000 : ℝ)^1024 ≤ (5000559960676669/5000000000000000 : ℝ)^4555 := by
      have hnat : (50024911742563996003 : ℕ)^1024*5000000000000000^4555 ≤ 5000559960676669^4555*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024911742563996003 50000000000000000000 5000559960676669 5000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000559960676669/5000000000000000 : ℝ)) (X := (50024911742563996003/50000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2703115569534599/50000000000000000000 : ℝ) ≤ ((3214390248835841743/3215000000000000000 : ℝ)+2*(219214710501/225050000000000 : ℝ)*(10983/100000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (3214390248835841743/3215000000000000000 : ℝ)+2*(219214710501/225050000000000 : ℝ)*(10983/100000 : ℝ)=(5000121531255667/5000000000000000 : ℝ) by norm_num, show 1+2*(2703115569534599/50000000000000000000 : ℝ)=(25002703115569534599/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24911742563996003/100000000000000000000 : ℝ)+(2703115569534599/50000000000000000000 : ℝ) ≤ ((3214390248835841743/3215000000000000000 : ℝ)+(219214710501/225050000000000 : ℝ)*((3871/25000 : ℝ)+(10983/100000 : ℝ)))^(4555/1024 : ℝ) := by
    rw [show (3214390248835841743/3215000000000000000 : ℝ)+(219214710501/225050000000000 : ℝ)*((3871/25000 : ℝ)+(10983/100000 : ℝ))=(625042593245771/625000000000000 : ℝ) by norm_num, show 1+(24911742563996003/100000000000000000000 : ℝ)+(2703115569534599/50000000000000000000 : ℝ)=(100030317973703065201/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24911742563996003/100000000000000000000 : ℝ) ≤ ((3214390248835841743/3215000000000000000 : ℝ)+2*(219214710501/225050000000000 : ℝ)*(3871/25000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (3214390248835841743/3215000000000000000 : ℝ)+2*(219214710501/225050000000000 : ℝ)*(3871/25000 : ℝ)=(5000559960676669/5000000000000000 : ℝ) by norm_num, show 1+2*(24911742563996003/100000000000000000000 : ℝ)=(50024911742563996003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3214390248835841743/3215000000000000000 : ℝ)*(X 1 0+X 2 0)+(219214710501/225050000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (10983/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (3214390248835841743/3215000000000000000 : ℝ)) (alpha := (219214710501/225050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3214390248835841743/3215000000000000000 : ℝ)*(X 0 1+X 2 1)+(219214710501/225050000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (10983/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (3214390248835841743/3215000000000000000 : ℝ)) (alpha := (219214710501/225050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3214390248835841743/3215000000000000000 : ℝ)*(X 0 2+X 1 2)+(219214710501/225050000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (10983/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (3214390248835841743/3215000000000000000 : ℝ)) (alpha := (219214710501/225050000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1841751219/10000000000 : ℝ)*X 0 0+(678862357/1250000000 : ℝ)*X 0 1+(2609248353/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675285411/5000000000 : ℝ)*X 1 0+(-975247187/5000000000 : ℝ)*X 1 1+(2609248359/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350570829/10000000000 : ℝ)*X 2 0+(2609248353/5000000000 : ℝ)*X 2 1+(-1950494381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4261462809/10000000000 : ℝ)*X 0 0+(4023422723/10000000000 : ℝ)*X 0 1+(2255588983/5000000000 : ℝ)*X 0 2+(4261462809/10000000000 : ℝ)*X 1 0+(4023422723/10000000000 : ℝ)*X 1 1+(2255588983/5000000000 : ℝ)*X 1 2+(4261462809/10000000000 : ℝ)*X 2 0+(4023422723/10000000000 : ℝ)*X 2 1+(2255588983/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-92088999/500000000 : ℝ)*X 0 0+(2609797091/5000000000 : ℝ)*X 0 1+(542979291/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1065382089/2500000000 : ℝ)*X 0 0+(2254328799/5000000000 : ℝ)*X 0 1+(4025960989/10000000000 : ℝ)*X 0 2+(1065382089/2500000000 : ℝ)*X 1 0+(2254328799/5000000000 : ℝ)*X 1 1+(4025960989/10000000000 : ℝ)*X 1 2+(1065382089/2500000000 : ℝ)*X 2 0+(2254328799/5000000000 : ℝ)*X 2 1+(4025960989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_s6_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (401886909221799144372243177/112525000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (607562583/100000000000000 : ℝ)*(base19) + (110175691/20000000000000 : ℝ)*(base23) + (8406223/25000000000000 : ℝ)*(lower2) + (48415043/50000000000000 : ℝ)*(upper3) + (11366151/25000000000000 : ℝ)*(upper5) + (337914362066247/10000000000000 : ℝ)*(major0) + (337914362066247/10000000000000 : ℝ)*(major1) + (337914362066247/10000000000000 : ℝ)*(major2) + (188322419340499/4000000000000 : ℝ)*(sp0) + (4708069309429657/100000000000000 : ℝ)*(sp1) + (588508670764223/12500000000000 : ℝ)*(sp2) + (2050212505098707/100000000000000 : ℝ)*(sp3) + (1886695953/20000000000000 : ℝ)*(sp4) + (4700182837/100000000000000 : ℝ)*(sp5) + (256277150660193/12500000000000 : ℝ)*(f.failure) + (58850873962403/1250000000000 : ℝ)*(f.sum) + (9969374920889/2250500000000000000000000000 : ℝ)*base65 + (3730655820441489647/225050000000000000000000000000000 : ℝ)*base67 + (829313754954589647/225050000000000000000000000000000 : ℝ)*base69 + (2915960986167889647/225050000000000000000000000000000 : ℝ)*base71 + (10332433163519/4501000000000000000000000000 : ℝ)*base73 + (1103088829493289647/225050000000000000000000000000000 : ℝ)*base75 + (2564986760773789647/225050000000000000000000000000000 : ℝ)*base77 + (4838523031807789647/225050000000000000000000000000000 : ℝ)*base79 + (12624796178563/4501000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (290523/1250000000000000000000 : ℝ)*base89 + (290523/1250000000000000000000 : ℝ)*base91 + (290523/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1530_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1530_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1530_box_0 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-40782157/250000000 : ℝ)*x 0 + (216035589/400000000 : ℝ)*x 1 + (675111173/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40782157/250000000 : ℝ)^4557 ≤ (482237510151/5000000000000 : ℝ)^3533 := by
    have hnat : (40782157 : ℕ)^4557*5000000000000^3533 ≤ 482237510151^3533*250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40782157 250000000 482237510151 5000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216035589/400000000 : ℝ)^4557 ≤ (11294406682589/25000000000000 : ℝ)^3533 := by
    have hnat : (216035589 : ℕ)^4557*25000000000000^3533 ≤ 11294406682589^3533*400000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216035589 400000000 11294406682589 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675111173/1250000000 : ℝ)^4557 ≤ (22588811525601/50000000000000 : ℝ)^3533 := by
    have hnat : (675111173 : ℕ)^4557*50000000000000^3533 ≤ 22588811525601^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675111173 1250000000 22588811525601 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40782157/250000000 : ℝ), (216035589/400000000 : ℝ), (675111173/1250000000 : ℝ)] ![(482237510151/5000000000000 : ℝ), (11294406682589/25000000000000 : ℝ), (22588811525601/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40782157/250000000 : ℝ)|^4557 ≤ (482237510151/5000000000000 : ℝ)^3533
        have hw : |(-40782157/250000000 : ℝ)|=(40782157/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216035589/400000000 : ℝ)|^4557 ≤ (11294406682589/25000000000000 : ℝ)^3533
        have hw : |(216035589/400000000 : ℝ)|=(216035589/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675111173/1250000000 : ℝ)|^4557 ≤ (22588811525601/50000000000000 : ℝ)^3533
        have hw : |(675111173/1250000000 : ℝ)|=(675111173/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_1 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270971697/10000000000 : ℝ)*x 0 + (-1811633727/10000000000 : ℝ)*x 1 + (5400889293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270971697/10000000000 : ℝ)^4557 ≤ (8756163197613/20000000000000 : ℝ)^3533 := by
    have hnat : (5270971697 : ℕ)^4557*20000000000000^3533 ≤ 8756163197613^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270971697 10000000000 8756163197613 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1811633727/10000000000 : ℝ)^4557 ≤ (11041561924591/100000000000000 : ℝ)^3533 := by
    have hnat : (1811633727 : ℕ)^4557*100000000000000^3533 ≤ 11041561924591^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811633727 10000000000 11041561924591 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5400889293/10000000000 : ℝ)^4557 ≤ (352950172417/781250000000 : ℝ)^3533 := by
    have hnat : (5400889293 : ℕ)^4557*781250000000^3533 ≤ 352950172417^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400889293 10000000000 352950172417 781250000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270971697/10000000000 : ℝ), (-1811633727/10000000000 : ℝ), (5400889293/10000000000 : ℝ)] ![(8756163197613/20000000000000 : ℝ), (11041561924591/100000000000000 : ℝ), (352950172417/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270971697/10000000000 : ℝ)|^4557 ≤ (8756163197613/20000000000000 : ℝ)^3533
        have hw : |(5270971697/10000000000 : ℝ)|=(5270971697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1811633727/10000000000 : ℝ)|^4557 ≤ (11041561924591/100000000000000 : ℝ)^3533
        have hw : |(-1811633727/10000000000 : ℝ)|=(1811633727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5400889293/10000000000 : ℝ)|^4557 ≤ (352950172417/781250000000 : ℝ)^3533
        have hw : |(5400889293/10000000000 : ℝ)|=(5400889293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_2 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270971859/10000000000 : ℝ)*x 0 + (5400889157/10000000000 : ℝ)*x 1 + (-1811633693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270971859/10000000000 : ℝ)^4557 ≤ (43780817723641/100000000000000 : ℝ)^3533 := by
    have hnat : (5270971859 : ℕ)^4557*100000000000000^3533 ≤ 43780817723641^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270971859 10000000000 43780817723641 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400889157/10000000000 : ℝ)^4557 ≤ (4517762060203/10000000000000 : ℝ)^3533 := by
    have hnat : (5400889157 : ℕ)^4557*10000000000000^3533 ≤ 4517762060203^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400889157 10000000000 4517762060203 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1811633693/10000000000 : ℝ)^4557 ≤ (5520780828653/50000000000000 : ℝ)^3533 := by
    have hnat : (1811633693 : ℕ)^4557*50000000000000^3533 ≤ 5520780828653^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1811633693 10000000000 5520780828653 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270971859/10000000000 : ℝ), (5400889157/10000000000 : ℝ), (-1811633693/10000000000 : ℝ)] ![(43780817723641/100000000000000 : ℝ), (4517762060203/10000000000000 : ℝ), (5520780828653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270971859/10000000000 : ℝ)|^4557 ≤ (43780817723641/100000000000000 : ℝ)^3533
        have hw : |(5270971859/10000000000 : ℝ)|=(5270971859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400889157/10000000000 : ℝ)|^4557 ≤ (4517762060203/10000000000000 : ℝ)^3533
        have hw : |(5400889157/10000000000 : ℝ)|=(5400889157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1811633693/10000000000 : ℝ)|^4557 ≤ (5520780828653/50000000000000 : ℝ)^3533
        have hw : |(-1811633693/10000000000 : ℝ)|=(1811633693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_3 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1115933777/2500000000 : ℝ)*x 0 + (520899351/1250000000 : ℝ)*x 1 + (1041798721/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1115933777/2500000000 : ℝ)^4557 ≤ (17665969448483/50000000000000 : ℝ)^3533 := by
    have hnat : (1115933777 : ℕ)^4557*50000000000000^3533 ≤ 17665969448483^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115933777 2500000000 17665969448483 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520899351/1250000000 : ℝ)^4557 ≤ (32334030166687/100000000000000 : ℝ)^3533 := by
    have hnat : (520899351 : ℕ)^4557*100000000000000^3533 ≤ 32334030166687^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520899351 1250000000 32334030166687 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1041798721/2500000000 : ℝ)^4557 ≤ (16167015463651/50000000000000 : ℝ)^3533 := by
    have hnat : (1041798721 : ℕ)^4557*50000000000000^3533 ≤ 16167015463651^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1041798721 2500000000 16167015463651 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1115933777/2500000000 : ℝ), (520899351/1250000000 : ℝ), (1041798721/2500000000 : ℝ)] ![(17665969448483/50000000000000 : ℝ), (32334030166687/100000000000000 : ℝ), (16167015463651/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1115933777/2500000000 : ℝ)|^4557 ≤ (17665969448483/50000000000000 : ℝ)^3533
        have hw : |(1115933777/2500000000 : ℝ)|=(1115933777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520899351/1250000000 : ℝ)|^4557 ≤ (32334030166687/100000000000000 : ℝ)^3533
        have hw : |(520899351/1250000000 : ℝ)|=(520899351/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1041798721/2500000000 : ℝ)|^4557 ≤ (16167015463651/50000000000000 : ℝ)^3533
        have hw : |(1041798721/2500000000 : ℝ)|=(1041798721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_4 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-514409177/2500000000 : ℝ)*x 0 + (1311040683/2500000000 : ℝ)*x 1 + (5244163309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514409177/2500000000 : ℝ)^4557 ≤ (6506184946293/50000000000000 : ℝ)^3533 := by
    have hnat : (514409177 : ℕ)^4557*50000000000000^3533 ≤ 6506184946293^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514409177 2500000000 6506184946293 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311040683/2500000000 : ℝ)^4557 ≤ (21746905980277/50000000000000 : ℝ)^3533 := by
    have hnat : (1311040683 : ℕ)^4557*50000000000000^3533 ≤ 21746905980277^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311040683 2500000000 21746905980277 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244163309/10000000000 : ℝ)^4557 ≤ (21746909066537/50000000000000 : ℝ)^3533 := by
    have hnat : (5244163309 : ℕ)^4557*50000000000000^3533 ≤ 21746909066537^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244163309 10000000000 21746909066537 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514409177/2500000000 : ℝ), (1311040683/2500000000 : ℝ), (5244163309/10000000000 : ℝ)] ![(6506184946293/50000000000000 : ℝ), (21746905980277/50000000000000 : ℝ), (21746909066537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514409177/2500000000 : ℝ)|^4557 ≤ (6506184946293/50000000000000 : ℝ)^3533
        have hw : |(-514409177/2500000000 : ℝ)|=(514409177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311040683/2500000000 : ℝ)|^4557 ≤ (21746905980277/50000000000000 : ℝ)^3533
        have hw : |(1311040683/2500000000 : ℝ)|=(1311040683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244163309/10000000000 : ℝ)|^4557 ≤ (21746909066537/50000000000000 : ℝ)^3533
        have hw : |(5244163309/10000000000 : ℝ)|=(5244163309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_5 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5379937823/10000000000 : ℝ)*x 0 + (-1876546451/10000000000 : ℝ)*x 1 + (104883257/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5379937823/10000000000 : ℝ)^4557 ≤ (5618962182619/12500000000000 : ℝ)^3533 := by
    have hnat : (5379937823 : ℕ)^4557*12500000000000^3533 ≤ 5618962182619^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5379937823 10000000000 5618962182619 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1876546451/10000000000 : ℝ)^4557 ≤ (2888622326803/25000000000000 : ℝ)^3533 := by
    have hnat : (1876546451 : ℕ)^4557*25000000000000^3533 ≤ 2888622326803^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876546451 10000000000 2888622326803 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104883257/200000000 : ℝ)^4557 ≤ (43493813222871/100000000000000 : ℝ)^3533 := by
    have hnat : (104883257 : ℕ)^4557*100000000000000^3533 ≤ 43493813222871^3533*200000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104883257 200000000 43493813222871 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5379937823/10000000000 : ℝ), (-1876546451/10000000000 : ℝ), (104883257/200000000 : ℝ)] ![(5618962182619/12500000000000 : ℝ), (2888622326803/25000000000000 : ℝ), (43493813222871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5379937823/10000000000 : ℝ)|^4557 ≤ (5618962182619/12500000000000 : ℝ)^3533
        have hw : |(5379937823/10000000000 : ℝ)|=(5379937823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1876546451/10000000000 : ℝ)|^4557 ≤ (2888622326803/25000000000000 : ℝ)^3533
        have hw : |(-1876546451/10000000000 : ℝ)|=(1876546451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104883257/200000000 : ℝ)|^4557 ≤ (43493813222871/100000000000000 : ℝ)^3533
        have hw : |(104883257/200000000 : ℝ)|=(104883257/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_6 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344984357/2500000000 : ℝ)*x 0 + (1311040723/2500000000 : ℝ)*x 1 + (-1876546929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344984357/2500000000 : ℝ)^4557 ≤ (1798067728159/4000000000000 : ℝ)^3533 := by
    have hnat : (1344984357 : ℕ)^4557*4000000000000^3533 ≤ 1798067728159^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344984357 2500000000 1798067728159 4000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311040723/2500000000 : ℝ)^4557 ≤ (43493813672171/100000000000000 : ℝ)^3533 := by
    have hnat : (1311040723 : ℕ)^4557*100000000000000^3533 ≤ 43493813672171^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311040723 2500000000 43493813672171 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876546929/10000000000 : ℝ)^4557 ≤ (5777246551731/50000000000000 : ℝ)^3533 := by
    have hnat : (1876546929 : ℕ)^4557*50000000000000^3533 ≤ 5777246551731^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876546929 10000000000 5777246551731 50000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344984357/2500000000 : ℝ), (1311040723/2500000000 : ℝ), (-1876546929/10000000000 : ℝ)] ![(1798067728159/4000000000000 : ℝ), (43493813672171/100000000000000 : ℝ), (5777246551731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344984357/2500000000 : ℝ)|^4557 ≤ (1798067728159/4000000000000 : ℝ)^3533
        have hw : |(1344984357/2500000000 : ℝ)|=(1344984357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311040723/2500000000 : ℝ)|^4557 ≤ (43493813672171/100000000000000 : ℝ)^3533
        have hw : |(1311040723/2500000000 : ℝ)|=(1311040723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876546929/10000000000 : ℝ)|^4557 ≤ (5777246551731/50000000000000 : ℝ)^3533
        have hw : |(-1876546929/10000000000 : ℝ)|=(1876546929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_7 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2028342483/5000000000 : ℝ)*x 0 + (546323531/1250000000 : ℝ)*x 1 + (4370587539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2028342483/5000000000 : ℝ)^4557 ≤ (6246462919701/20000000000000 : ℝ)^3533 := by
    have hnat : (2028342483 : ℕ)^4557*20000000000000^3533 ≤ 6246462919701^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028342483 5000000000 6246462919701 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546323531/1250000000 : ℝ)^4557 ≤ (34383846287839/100000000000000 : ℝ)^3533 := by
    have hnat : (546323531 : ℕ)^4557*100000000000000^3533 ≤ 34383846287839^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546323531 1250000000 34383846287839 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4370587539/10000000000 : ℝ)^4557 ≤ (34383839093413/100000000000000 : ℝ)^3533 := by
    have hnat : (4370587539 : ℕ)^4557*100000000000000^3533 ≤ 34383839093413^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370587539 10000000000 34383839093413 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2028342483/5000000000 : ℝ), (546323531/1250000000 : ℝ), (4370587539/10000000000 : ℝ)] ![(6246462919701/20000000000000 : ℝ), (34383846287839/100000000000000 : ℝ), (34383839093413/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2028342483/5000000000 : ℝ)|^4557 ≤ (6246462919701/20000000000000 : ℝ)^3533
        have hw : |(2028342483/5000000000 : ℝ)|=(2028342483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546323531/1250000000 : ℝ)|^4557 ≤ (34383846287839/100000000000000 : ℝ)^3533
        have hw : |(546323531/1250000000 : ℝ)|=(546323531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4370587539/10000000000 : ℝ)|^4557 ≤ (34383839093413/100000000000000 : ℝ)^3533
        have hw : |(4370587539/10000000000 : ℝ)|=(4370587539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_8 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-983723711/5000000000 : ℝ)*x 0 + (32088559/62500000 : ℝ)*x 1 + (677660973/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (983723711/5000000000 : ℝ)^4557 ≤ (2456286146391/20000000000000 : ℝ)^3533 := by
    have hnat : (983723711 : ℕ)^4557*20000000000000^3533 ≤ 2456286146391^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983723711 5000000000 2456286146391 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32088559/62500000 : ℝ)^4557 ≤ (42320741284749/100000000000000 : ℝ)^3533 := by
    have hnat : (32088559 : ℕ)^4557*100000000000000^3533 ≤ 42320741284749^3533*62500000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32088559 62500000 42320741284749 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (677660973/1250000000 : ℝ)^4557 ≤ (45397827971889/100000000000000 : ℝ)^3533 := by
    have hnat : (677660973 : ℕ)^4557*100000000000000^3533 ≤ 45397827971889^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677660973 1250000000 45397827971889 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-983723711/5000000000 : ℝ), (32088559/62500000 : ℝ), (677660973/1250000000 : ℝ)] ![(2456286146391/20000000000000 : ℝ), (42320741284749/100000000000000 : ℝ), (45397827971889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-983723711/5000000000 : ℝ)|^4557 ≤ (2456286146391/20000000000000 : ℝ)^3533
        have hw : |(-983723711/5000000000 : ℝ)|=(983723711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(32088559/62500000 : ℝ)|^4557 ≤ (42320741284749/100000000000000 : ℝ)^3533
        have hw : |(32088559/62500000 : ℝ)|=(32088559/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(677660973/1250000000 : ℝ)|^4557 ≤ (45397827971889/100000000000000 : ℝ)^3533
        have hw : |(677660973/1250000000 : ℝ)|=(677660973/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_9 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256784143/10000000000 : ℝ)*x 0 + (-225367939/1250000000 : ℝ)*x 1 + (5421287893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256784143/10000000000 : ℝ)^4557 ≤ (43628877941141/100000000000000 : ℝ)^3533 := by
    have hnat : (5256784143 : ℕ)^4557*100000000000000^3533 ≤ 43628877941141^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256784143 10000000000 43628877941141 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (225367939/1250000000 : ℝ)^4557 ≤ (2743323225957/25000000000000 : ℝ)^3533 := by
    have hnat : (225367939 : ℕ)^4557*25000000000000^3533 ≤ 2743323225957^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225367939 1250000000 2743323225957 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5421287893/10000000000 : ℝ)^4557 ≤ (45397829149209/100000000000000 : ℝ)^3533 := by
    have hnat : (5421287893 : ℕ)^4557*100000000000000^3533 ≤ 45397829149209^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421287893 10000000000 45397829149209 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256784143/10000000000 : ℝ), (-225367939/1250000000 : ℝ), (5421287893/10000000000 : ℝ)] ![(43628877941141/100000000000000 : ℝ), (2743323225957/25000000000000 : ℝ), (45397829149209/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256784143/10000000000 : ℝ)|^4557 ≤ (43628877941141/100000000000000 : ℝ)^3533
        have hw : |(5256784143/10000000000 : ℝ)|=(5256784143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-225367939/1250000000 : ℝ)|^4557 ≤ (2743323225957/25000000000000 : ℝ)^3533
        have hw : |(-225367939/1250000000 : ℝ)|=(225367939/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5421287893/10000000000 : ℝ)|^4557 ≤ (45397829149209/100000000000000 : ℝ)^3533
        have hw : |(5421287893/10000000000 : ℝ)|=(5421287893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_10 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314196029/2500000000 : ℝ)*x 0 + (5421287823/10000000000 : ℝ)*x 1 + (-360588729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314196029/2500000000 : ℝ)^4557 ≤ (5453609706513/12500000000000 : ℝ)^3533 := by
    have hnat : (1314196029 : ℕ)^4557*12500000000000^3533 ≤ 5453609706513^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314196029 2500000000 5453609706513 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5421287823/10000000000 : ℝ)^4557 ≤ (11349457098283/25000000000000 : ℝ)^3533 := by
    have hnat : (5421287823 : ℕ)^4557*25000000000000^3533 ≤ 11349457098283^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421287823 10000000000 11349457098283 25000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (360588729/2000000000 : ℝ)^4557 ≤ (10973293947927/100000000000000 : ℝ)^3533 := by
    have hnat : (360588729 : ℕ)^4557*100000000000000^3533 ≤ 10973293947927^3533*2000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360588729 2000000000 10973293947927 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314196029/2500000000 : ℝ), (5421287823/10000000000 : ℝ), (-360588729/2000000000 : ℝ)] ![(5453609706513/12500000000000 : ℝ), (11349457098283/25000000000000 : ℝ), (10973293947927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314196029/2500000000 : ℝ)|^4557 ≤ (5453609706513/12500000000000 : ℝ)^3533
        have hw : |(1314196029/2500000000 : ℝ)|=(1314196029/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5421287823/10000000000 : ℝ)|^4557 ≤ (11349457098283/25000000000000 : ℝ)^3533
        have hw : |(5421287823/10000000000 : ℝ)|=(5421287823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-360588729/2000000000 : ℝ)|^4557 ≤ (10973293947927/100000000000000 : ℝ)^3533
        have hw : |(-360588729/2000000000 : ℝ)|=(360588729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_11 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2257782129/5000000000 : ℝ)*x 0 + (82813801/200000000 : ℝ)*x 1 + (4140689817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257782129/5000000000 : ℝ)^4557 ≤ (3586197652757/10000000000000 : ℝ)^3533 := by
    have hnat : (2257782129 : ℕ)^4557*10000000000000^3533 ≤ 3586197652757^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257782129 5000000000 3586197652757 10000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82813801/200000000 : ℝ)^4557 ≤ (32069012896587/100000000000000 : ℝ)^3533 := by
    have hnat : (82813801 : ℕ)^4557*100000000000000^3533 ≤ 32069012896587^3533*200000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82813801 200000000 32069012896587 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4140689817/10000000000 : ℝ)^4557 ≤ (32069010569009/100000000000000 : ℝ)^3533 := by
    have hnat : (4140689817 : ℕ)^4557*100000000000000^3533 ≤ 32069010569009^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4140689817 10000000000 32069010569009 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257782129/5000000000 : ℝ), (82813801/200000000 : ℝ), (4140689817/10000000000 : ℝ)] ![(3586197652757/10000000000000 : ℝ), (32069012896587/100000000000000 : ℝ), (32069010569009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257782129/5000000000 : ℝ)|^4557 ≤ (3586197652757/10000000000000 : ℝ)^3533
        have hw : |(2257782129/5000000000 : ℝ)|=(2257782129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82813801/200000000 : ℝ)|^4557 ≤ (32069012896587/100000000000000 : ℝ)^3533
        have hw : |(82813801/200000000 : ℝ)|=(82813801/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4140689817/10000000000 : ℝ)|^4557 ≤ (32069010569009/100000000000000 : ℝ)^3533
        have hw : |(4140689817/10000000000 : ℝ)|=(4140689817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_12 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1721330337/10000000000 : ℝ)*x 0 + (5507407229/10000000000 : ℝ)*x 1 + (5229124511/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1721330337/10000000000 : ℝ)^4557 ≤ (10336847999169/100000000000000 : ℝ)^3533 := by
    have hnat : (1721330337 : ℕ)^4557*100000000000000^3533 ≤ 10336847999169^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1721330337 10000000000 10336847999169 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5507407229/10000000000 : ℝ)^4557 ≤ (46330146130329/100000000000000 : ℝ)^3533 := by
    have hnat : (5507407229 : ℕ)^4557*100000000000000^3533 ≤ 46330146130329^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507407229 10000000000 46330146130329 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229124511/10000000000 : ℝ)^4557 ≤ (8666601171629/20000000000000 : ℝ)^3533 := by
    have hnat : (5229124511 : ℕ)^4557*20000000000000^3533 ≤ 8666601171629^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229124511 10000000000 8666601171629 20000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1721330337/10000000000 : ℝ), (5507407229/10000000000 : ℝ), (5229124511/10000000000 : ℝ)] ![(10336847999169/100000000000000 : ℝ), (46330146130329/100000000000000 : ℝ), (8666601171629/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1721330337/10000000000 : ℝ)|^4557 ≤ (10336847999169/100000000000000 : ℝ)^3533
        have hw : |(-1721330337/10000000000 : ℝ)|=(1721330337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5507407229/10000000000 : ℝ)|^4557 ≤ (46330146130329/100000000000000 : ℝ)^3533
        have hw : |(5507407229/10000000000 : ℝ)|=(5507407229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229124511/10000000000 : ℝ)|^4557 ≤ (8666601171629/20000000000000 : ℝ)^3533
        have hw : |(5229124511/10000000000 : ℝ)|=(5229124511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_13 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695196723/5000000000 : ℝ)*x 0 + (-117662423/625000000 : ℝ)*x 1 + (5229124897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695196723/5000000000 : ℝ)^4557 ≤ (5633051384817/12500000000000 : ℝ)^3533 := by
    have hnat : (2695196723 : ℕ)^4557*12500000000000^3533 ≤ 5633051384817^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695196723 5000000000 5633051384817 12500000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117662423/625000000 : ℝ)^4557 ≤ (11602578920081/100000000000000 : ℝ)^3533 := by
    have hnat : (117662423 : ℕ)^4557*100000000000000^3533 ≤ 11602578920081^3533*625000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117662423 625000000 11602578920081 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5229124897/10000000000 : ℝ)^4557 ≤ (43333009983987/100000000000000 : ℝ)^3533 := by
    have hnat : (5229124897 : ℕ)^4557*100000000000000^3533 ≤ 43333009983987^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229124897 10000000000 43333009983987 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695196723/5000000000 : ℝ), (-117662423/625000000 : ℝ), (5229124897/10000000000 : ℝ)] ![(5633051384817/12500000000000 : ℝ), (11602578920081/100000000000000 : ℝ), (43333009983987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695196723/5000000000 : ℝ)|^4557 ≤ (5633051384817/12500000000000 : ℝ)^3533
        have hw : |(2695196723/5000000000 : ℝ)|=(2695196723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-117662423/625000000 : ℝ)|^4557 ≤ (11602578920081/100000000000000 : ℝ)^3533
        have hw : |(-117662423/625000000 : ℝ)|=(117662423/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5229124897/10000000000 : ℝ)|^4557 ≤ (43333009983987/100000000000000 : ℝ)^3533
        have hw : |(5229124897/10000000000 : ℝ)|=(5229124897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_14 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1347598153/2500000000 : ℝ)*x 0 + (653640611/1250000000 : ℝ)*x 1 + (-235324989/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1347598153/2500000000 : ℝ)^4557 ≤ (2816525130333/6250000000000 : ℝ)^3533 := by
    have hnat : (1347598153 : ℕ)^4557*6250000000000^3533 ≤ 2816525130333^3533*2500000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347598153 2500000000 2816525130333 6250000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653640611/1250000000 : ℝ)^4557 ≤ (43333009887789/100000000000000 : ℝ)^3533 := by
    have hnat : (653640611 : ℕ)^4557*100000000000000^3533 ≤ 43333009887789^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653640611 1250000000 43333009887789 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235324989/1250000000 : ℝ)^4557 ≤ (11602588014149/100000000000000 : ℝ)^3533 := by
    have hnat : (235324989 : ℕ)^4557*100000000000000^3533 ≤ 11602588014149^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235324989 1250000000 11602588014149 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1347598153/2500000000 : ℝ), (653640611/1250000000 : ℝ), (-235324989/1250000000 : ℝ)] ![(2816525130333/6250000000000 : ℝ), (43333009887789/100000000000000 : ℝ), (11602588014149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1347598153/2500000000 : ℝ)|^4557 ≤ (2816525130333/6250000000000 : ℝ)^3533
        have hw : |(1347598153/2500000000 : ℝ)|=(1347598153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653640611/1250000000 : ℝ)|^4557 ≤ (43333009887789/100000000000000 : ℝ)^3533
        have hw : |(653640611/1250000000 : ℝ)|=(653640611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-235324989/1250000000 : ℝ)|^4557 ≤ (11602588014149/100000000000000 : ℝ)^3533
        have hw : |(-235324989/1250000000 : ℝ)|=(235324989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1530_box_15 (p : ℝ) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (502095561/1250000000 : ℝ)*x 0 + (4390081217/10000000000 : ℝ)*x 1 + (2195040457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502095561/1250000000 : ℝ)^4557 ≤ (1927278346883/6250000000000 : ℝ)^3533 := by
    have hnat : (502095561 : ℕ)^4557*6250000000000^3533 ≤ 1927278346883^3533*1250000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502095561 1250000000 1927278346883 6250000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4390081217/10000000000 : ℝ)^4557 ≤ (34581774756257/100000000000000 : ℝ)^3533 := by
    have hnat : (4390081217 : ℕ)^4557*100000000000000^3533 ≤ 34581774756257^3533*10000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4390081217 10000000000 34581774756257 100000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195040457/5000000000 : ℝ)^4557 ≤ (1729088583883/5000000000000 : ℝ)^3533 := by
    have hnat : (2195040457 : ℕ)^4557*5000000000000^3533 ≤ 1729088583883^3533*5000000000^4557 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195040457 5000000000 1729088583883 5000000000000 4557 3533 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4557/1024 : ℝ)) 4557 3533 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(502095561/1250000000 : ℝ), (4390081217/10000000000 : ℝ), (2195040457/5000000000 : ℝ)] ![(1927278346883/6250000000000 : ℝ), (34581774756257/100000000000000 : ℝ), (1729088583883/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(502095561/1250000000 : ℝ)|^4557 ≤ (1927278346883/6250000000000 : ℝ)^3533
        have hw : |(502095561/1250000000 : ℝ)|=(502095561/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4390081217/10000000000 : ℝ)|^4557 ≤ (34581774756257/100000000000000 : ℝ)^3533
        have hw : |(4390081217/10000000000 : ℝ)|=(4390081217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2195040457/5000000000 : ℝ)|^4557 ≤ (1729088583883/5000000000000 : ℝ)^3533
        have hw : |(2195040457/5000000000 : ℝ)|=(2195040457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1530_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(15941/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58713/100000 : ℝ) ∧ (80511/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86117/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1373/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1373/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1373/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1373/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1373/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1373/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1373/12500 : ℝ) ^ (4555/1024 : ℝ) ≤ (5408421069035553/100000000000000000000 : ℝ) := by
    have hpowers : (1373/12500 : ℝ)^4555 ≤ (5408421069035553/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1373 : ℕ)^4555*100000000000000000000^1024 ≤ 5408421069035553^1024*12500^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1373 12500 5408421069035553 100000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1373/12500 : ℝ)) (X := (5408421069035553/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4555/1024 : ℝ) ≤ (24911742563996003/100000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4555 ≤ (24911742563996003/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4555*100000000000000000000^1024 ≤ 24911742563996003^1024*25000^4555 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 24911742563996003 100000000000000000000 4555 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (24911742563996003/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005408421069035553/50000000000000000000 : ℝ) ≤ (10000243160965793/10000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (50005408421069035553/50000000000000000000 : ℝ)^1024 ≤ (10000243160965793/10000000000000000 : ℝ)^4555 := by
      have hnat : (50005408421069035553 : ℕ)^1024*10000000000000000^4555 ≤ 10000243160965793^4555*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005408421069035553 50000000000000000000 10000243160965793 10000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000243160965793/10000000000000000 : ℝ)) (X := (50005408421069035553/50000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25007580040908257889/25000000000000000000 : ℝ) ≤ (2500170385288031/2500000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (25007580040908257889/25000000000000000000 : ℝ)^1024 ≤ (2500170385288031/2500000000000000 : ℝ)^4555 := by
      have hnat : (25007580040908257889 : ℕ)^1024*2500000000000000^4555 ≤ 2500170385288031^4555*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007580040908257889 25000000000000000000 2500170385288031 2500000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500170385288031/2500000000000000 : ℝ)) (X := (25007580040908257889/25000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024911742563996003/50000000000000000000 : ℝ) ≤ (2000223984267691/2000000000000000 : ℝ) ^ (4555/1024 : ℝ) := by
    have hpowers : (50024911742563996003/50000000000000000000 : ℝ)^1024 ≤ (2000223984267691/2000000000000000 : ℝ)^4555 := by
      have hnat : (50024911742563996003 : ℕ)^1024*2000000000000000^4555 ≤ 2000223984267691^4555*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024911742563996003 50000000000000000000 2000223984267691 2000000000000000 1024 4555 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000223984267691/2000000000000000 : ℝ)) (X := (50024911742563996003/50000000000000000000 : ℝ)) (by norm_num) 4555 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5408421069035553/100000000000000000000 : ℝ) ≤ ((3749288657367729091/3750000000000000000 : ℝ)+2*(146126728777/150000000000000 : ℝ)*(1373/12500 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (3749288657367729091/3750000000000000000 : ℝ)+2*(146126728777/150000000000000 : ℝ)*(1373/12500 : ℝ)=(10000243160965793/10000000000000000 : ℝ) by norm_num, show 1+2*(5408421069035553/100000000000000000000 : ℝ)=(50005408421069035553/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24911742563996003/100000000000000000000 : ℝ)+(5408421069035553/100000000000000000000 : ℝ) ≤ ((3749288657367729091/3750000000000000000 : ℝ)+(146126728777/150000000000000 : ℝ)*((3871/25000 : ℝ)+(1373/12500 : ℝ)))^(4555/1024 : ℝ) := by
    rw [show (3749288657367729091/3750000000000000000 : ℝ)+(146126728777/150000000000000 : ℝ)*((3871/25000 : ℝ)+(1373/12500 : ℝ))=(2500170385288031/2500000000000000 : ℝ) by norm_num, show 1+(24911742563996003/100000000000000000000 : ℝ)+(5408421069035553/100000000000000000000 : ℝ)=(25007580040908257889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24911742563996003/100000000000000000000 : ℝ) ≤ ((3749288657367729091/3750000000000000000 : ℝ)+2*(146126728777/150000000000000 : ℝ)*(3871/25000 : ℝ))^(4555/1024 : ℝ) := by
    rw [show (3749288657367729091/3750000000000000000 : ℝ)+2*(146126728777/150000000000000 : ℝ)*(3871/25000 : ℝ)=(2000223984267691/2000000000000000 : ℝ) by norm_num, show 1+2*(24911742563996003/100000000000000000000 : ℝ)=(50024911742563996003/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3749288657367729091/3750000000000000000 : ℝ)*(X 1 0+X 2 0)+(146126728777/150000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (3749288657367729091/3750000000000000000 : ℝ)) (alpha := (146126728777/150000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3749288657367729091/3750000000000000000 : ℝ)*(X 0 1+X 2 1)+(146126728777/150000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (3749288657367729091/3750000000000000000 : ℝ)) (alpha := (146126728777/150000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3749288657367729091/3750000000000000000 : ℝ)*(X 0 2+X 1 2)+(146126728777/150000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4555/1024 : ℝ)) (lo := (1373/12500 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (3749288657367729091/3750000000000000000 : ℝ)) (alpha := (146126728777/150000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-40782157/250000000 : ℝ)*X 0 0+(216035589/400000000 : ℝ)*X 0 1+(675111173/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270971697/10000000000 : ℝ)*X 1 0+(-1811633727/10000000000 : ℝ)*X 1 1+(5400889293/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270971859/10000000000 : ℝ)*X 2 0+(5400889157/10000000000 : ℝ)*X 2 1+(-1811633693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1115933777/2500000000 : ℝ)*X 0 0+(520899351/1250000000 : ℝ)*X 0 1+(1041798721/2500000000 : ℝ)*X 0 2+(1115933777/2500000000 : ℝ)*X 1 0+(520899351/1250000000 : ℝ)*X 1 1+(1041798721/2500000000 : ℝ)*X 1 2+(1115933777/2500000000 : ℝ)*X 2 0+(520899351/1250000000 : ℝ)*X 2 1+(1041798721/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-514409177/2500000000 : ℝ)*X 0 0+(1311040683/2500000000 : ℝ)*X 0 1+(5244163309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5379937823/10000000000 : ℝ)*X 1 0+(-1876546451/10000000000 : ℝ)*X 1 1+(104883257/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1344984357/2500000000 : ℝ)*X 2 0+(1311040723/2500000000 : ℝ)*X 2 1+(-1876546929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2028342483/5000000000 : ℝ)*X 0 0+(546323531/1250000000 : ℝ)*X 0 1+(4370587539/10000000000 : ℝ)*X 0 2+(2028342483/5000000000 : ℝ)*X 1 0+(546323531/1250000000 : ℝ)*X 1 1+(4370587539/10000000000 : ℝ)*X 1 2+(2028342483/5000000000 : ℝ)*X 2 0+(546323531/1250000000 : ℝ)*X 2 1+(4370587539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-983723711/5000000000 : ℝ)*X 0 0+(32088559/62500000 : ℝ)*X 0 1+(677660973/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5256784143/10000000000 : ℝ)*X 1 0+(-225367939/1250000000 : ℝ)*X 1 1+(5421287893/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314196029/2500000000 : ℝ)*X 2 0+(5421287823/10000000000 : ℝ)*X 2 1+(-360588729/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2257782129/5000000000 : ℝ)*X 0 0+(82813801/200000000 : ℝ)*X 0 1+(4140689817/10000000000 : ℝ)*X 0 2+(2257782129/5000000000 : ℝ)*X 1 0+(82813801/200000000 : ℝ)*X 1 1+(4140689817/10000000000 : ℝ)*X 1 2+(2257782129/5000000000 : ℝ)*X 2 0+(82813801/200000000 : ℝ)*X 2 1+(4140689817/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1721330337/10000000000 : ℝ)*X 0 0+(5507407229/10000000000 : ℝ)*X 0 1+(5229124511/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((2695196723/5000000000 : ℝ)*X 1 0+(-117662423/625000000 : ℝ)*X 1 1+(5229124897/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1347598153/2500000000 : ℝ)*X 2 0+(653640611/1250000000 : ℝ)*X 2 1+(-235324989/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((502095561/1250000000 : ℝ)*X 0 0+(4390081217/10000000000 : ℝ)*X 0 1+(2195040457/5000000000 : ℝ)*X 0 2+(502095561/1250000000 : ℝ)*X 1 0+(4390081217/10000000000 : ℝ)*X 1 1+(2195040457/5000000000 : ℝ)*X 1 2+(502095561/1250000000 : ℝ)*X 2 0+(4390081217/10000000000 : ℝ)*X 2 1+(2195040457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1530_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15941/25000 : ℝ) ≤ (-9962759192091094866189828592659/15625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (136980969/100000000000000 : ℝ)*(lower0) + (63815037/100000000000000 : ℝ)*(upper1) + (203284437/100000000000000 : ℝ)*(lower4) + (1124931229948251/50000000000000 : ℝ)*(major0) + (1124931229948251/50000000000000 : ℝ)*(major1) + (1124931229948251/50000000000000 : ℝ)*(major2) + (2399875561/50000000000000 : ℝ)*(sp1) + (12015387781/100000000000000 : ℝ)*(sp2) + (514941521/20000000000000 : ℝ)*(sp3) + (1577961473831361/50000000000000 : ℝ)*(sp4) + (1577961008023667/50000000000000 : ℝ)*(sp5) + (788978700102669/25000000000000 : ℝ)*(sp6) + (682524707781699/50000000000000 : ℝ)*(sp7) + (1934067867/50000000000000 : ℝ)*(sp12) + (1365051990271003/100000000000000 : ℝ)*(f.failure) + (394490851974807/12500000000000 : ℝ)*(f.sum) + (3553637419491/1250000000000000000000000000 : ℝ)*base66 + (46420495110685053/62500000000000000000000000000000 : ℝ)*base68 + (96112643860685053/62500000000000000000000000000000 : ℝ)*base70 + (83577969485685053/62500000000000000000000000000000 : ℝ)*base72 + (15533198596991/1250000000000000000000000000 : ℝ)*base74 + (271072639014314947/62500000000000000000000000000000 : ℝ)*base75 + (230810987673185053/62500000000000000000000000000000 : ℝ)*base78 + (645803496298185053/62500000000000000000000000000000 : ℝ)*base80 + (5687285291759/1250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (82237433/10000000000000000000000 : ℝ)*base89 + (82237433/10000000000000000000000 : ℝ)*base91 + (82237433/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58713/100000 : ℝ) ≤ (183484449186396978802122923/312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (14951697/50000000000000 : ℝ)*(lower1) + (6978239/50000000000000 : ℝ)*(lower2) + (77643/312500000000 : ℝ)*(upper4) + (145458960883237/6250000000000 : ℝ)*(major0) + (145458960883237/6250000000000 : ℝ)*(major1) + (145458960883237/6250000000000 : ℝ)*(major2) + (805762422484243/25000000000000 : ℝ)*(sp0) + (3223020652107597/100000000000000 : ℝ)*(sp1) + (322301119985859/10000000000000 : ℝ)*(sp2) + (70602984456841/5000000000000 : ℝ)*(sp3) + (2053094649/100000000000000 : ℝ)*(sp7) + (455189407/12500000000000 : ℝ)*(sp8) + (3267934463/10000000000000 : ℝ)*(sp9) + (21065796819/50000000000000 : ℝ)*(sp10) + (1412061742231469/100000000000000 : ℝ)*(f.failure) + (805763332863057/25000000000000 : ℝ)*(f.sum) + (5958704098327/937500000000000000000000000 : ℝ)*base66 + (65637855890877433/23437500000000000000000000000000 : ℝ)*base68 + (23517438070060067/23437500000000000000000000000000 : ℝ)*base69 + (63713640023185067/23437500000000000000000000000000 : ℝ)*base71 + (2325736254779/1875000000000000000000000000 : ℝ)*base74 + (117068557780997567/23437500000000000000000000000000 : ℝ)*base75 + (144237655734627433/23437500000000000000000000000000 : ℝ)*base78 + (96495419109627433/23437500000000000000000000000000 : ℝ)*base80 + (12064976161471/1875000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (7363359/10000000000000000000000 : ℝ)*base89 + (7363359/10000000000000000000000 : ℝ)*base91 + (7363359/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80511/100000 : ℝ) ≤ (25160315758408020692836709149967/31250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (690263/2500000000000 : ℝ)*(upper1) + (7109469/25000000000000 : ℝ)*(upper2) + (21081749/50000000000000 : ℝ)*(upper3) + (250133/50000000000000 : ℝ)*(lower5) + (1259524525840363/50000000000000 : ℝ)*(major0) + (1259524525840363/50000000000000 : ℝ)*(major1) + (1259524525840363/50000000000000 : ℝ)*(major2) + (969775773/50000000000000 : ℝ)*(sp0) + (13416043979/100000000000000 : ℝ)*(sp1) + (2569013601/20000000000000 : ℝ)*(sp3) + (217680235454083/6250000000000 : ℝ)*(sp8) + (1741436145386447/50000000000000 : ℝ)*(sp9) + (1741442853408437/50000000000000 : ℝ)*(sp10) + (764180940667133/50000000000000 : ℝ)*(sp11) + (1528374726402271/100000000000000 : ℝ)*(f.failure) + (1741442853408437/50000000000000 : ℝ)*(f.sum) + (15901684456051/3750000000000000000000000000 : ℝ)*base65 + (1429807866276624967/187500000000000000000000000000000 : ℝ)*base68 + (1157404875276624967/187500000000000000000000000000000 : ℝ)*base70 + (608700784410875033/187500000000000000000000000000000 : ℝ)*base71 + (18818129320199/3750000000000000000000000000 : ℝ)*base74 + (686161054785875033/187500000000000000000000000000000 : ℝ)*base75 + (92271188348375033/187500000000000000000000000000000 : ℝ)*base77 + (104188858973375033/187500000000000000000000000000000 : ℝ)*base79 + (32661862318949/3750000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (13919781/10000000000000000000000 : ℝ)*base89 + (13919781/10000000000000000000000 : ℝ)*base91 + (13919781/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-86117/100000 : ℝ) ≤ (-5382141028459603653098989690531/6250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (21338433/25000000000000 : ℝ)*(lower0) + (79213887/100000000000000 : ℝ)*(upper1) + (212271901/100000000000000 : ℝ)*(upper3) + (55014607/12500000000000 : ℝ)*(lower4) + (255856200224159/10000000000000 : ℝ)*(major0) + (255856200224159/10000000000000 : ℝ)*(major1) + (255856200224159/10000000000000 : ℝ)*(major2) + (1878584251/50000000000000 : ℝ)*(sp4) + (8394196203/6250000000000 : ℝ)*(sp6) + (31318757643/25000000000000 : ℝ)*(sp7) + (56148073508769/1562500000000 : ℝ)*(sp12) + (1796740230864859/50000000000000 : ℝ)*(sp13) + (3593346154590469/100000000000000 : ℝ)*(sp14) + (388055754968667/25000000000000 : ℝ)*(sp15) + (38808707372631/2500000000000 : ℝ)*(f.failure) + (1796740230864859/50000000000000 : ℝ)*(f.sum) + (29946072457/750000000000000000000000000 : ℝ)*base66 + (285050247676115531/37500000000000000000000000000000 : ℝ)*base68 + (809182479298884469/37500000000000000000000000000000 : ℝ)*base69 + (183202948576115531/37500000000000000000000000000000 : ℝ)*base72 + (552014882543/750000000000000000000000000 : ℝ)*base73 + (56402583598884469/37500000000000000000000000000000 : ℝ)*base75 + (39786483976115531/37500000000000000000000000000000 : ℝ)*base78 + (196166988676115531/37500000000000000000000000000000 : ℝ)*base80 + (8583105368543/750000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (361741/250000000000000000000 : ℝ)*base89 + (361741/250000000000000000000 : ℝ)*base91 + (361741/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1530_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1373/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15941/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58713/100000 : ℝ) else (80511/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86117/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1530_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1530_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15941/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58713/100000 : ℝ) else (80511/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86117/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1530_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1530_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4555/1024 : ℝ) ≤ p) (hpb : p ≤ (4557/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (164818811/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10983/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15941/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58713/100000 : ℝ) else (80511/100000 : ℝ) ≤ X j i ∧ X j i ≤ (86117/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1530_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
