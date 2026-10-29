-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1767_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:30:20.014315+00:00
-- url     : https://prove2.me/submissions/edc7ddca-2cfb-40ce-9f34-88f2c74e58ee

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
theorem support_rectangle_w1767_s3_0 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283404847/2500000000 : ℝ)*x 0 + (273753473/500000000 : ℝ)*x 1 + (5085223357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283404847/2500000000 : ℝ)^6047 ≤ (1818230163333/25000000000000 : ℝ)^5023 := by
    have hnat : (283404847 : ℕ)^6047*25000000000000^5023 ≤ 1818230163333^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283404847 2500000000 1818230163333 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273753473/500000000 : ℝ)^6047 ≤ (24211804798953/50000000000000 : ℝ)^5023 := by
    have hnat : (273753473 : ℕ)^6047*50000000000000^5023 ≤ 24211804798953^5023*500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273753473 500000000 24211804798953 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5085223357/10000000000 : ℝ)^6047 ≤ (1107586743413/2500000000000 : ℝ)^5023 := by
    have hnat : (5085223357 : ℕ)^6047*2500000000000^5023 ≤ 1107586743413^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085223357 10000000000 1107586743413 2500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283404847/2500000000 : ℝ), (273753473/500000000 : ℝ), (5085223357/10000000000 : ℝ)] ![(1818230163333/25000000000000 : ℝ), (24211804798953/50000000000000 : ℝ), (1107586743413/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283404847/2500000000 : ℝ)|^6047 ≤ (1818230163333/25000000000000 : ℝ)^5023
        have hw : |(-283404847/2500000000 : ℝ)|=(283404847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(273753473/500000000 : ℝ)|^6047 ≤ (24211804798953/50000000000000 : ℝ)^5023
        have hw : |(273753473/500000000 : ℝ)|=(273753473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5085223357/10000000000 : ℝ)|^6047 ≤ (1107586743413/2500000000000 : ℝ)^5023
        have hw : |(5085223357/10000000000 : ℝ)|=(5085223357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s3_1 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5324547687/10000000000 : ℝ)*x 0 + (-33424559/250000000 : ℝ)*x 1 + (203408937/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5324547687/10000000000 : ℝ)^6047 ≤ (46825465670331/100000000000000 : ℝ)^5023 := by
    have hnat : (5324547687 : ℕ)^6047*100000000000000^5023 ≤ 46825465670331^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5324547687 10000000000 46825465670331 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33424559/250000000 : ℝ)^6047 ≤ (2217765966183/25000000000000 : ℝ)^5023 := by
    have hnat : (33424559 : ℕ)^6047*25000000000000^5023 ≤ 2217765966183^5023*250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33424559 250000000 2217765966183 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203408937/400000000 : ℝ)^6047 ≤ (11075867612431/25000000000000 : ℝ)^5023 := by
    have hnat : (203408937 : ℕ)^6047*25000000000000^5023 ≤ 11075867612431^5023*400000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203408937 400000000 11075867612431 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5324547687/10000000000 : ℝ), (-33424559/250000000 : ℝ), (203408937/400000000 : ℝ)] ![(46825465670331/100000000000000 : ℝ), (2217765966183/25000000000000 : ℝ), (11075867612431/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5324547687/10000000000 : ℝ)|^6047 ≤ (46825465670331/100000000000000 : ℝ)^5023
        have hw : |(5324547687/10000000000 : ℝ)|=(5324547687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-33424559/250000000 : ℝ)|^6047 ≤ (2217765966183/25000000000000 : ℝ)^5023
        have hw : |(-33424559/250000000 : ℝ)|=(33424559/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(203408937/400000000 : ℝ)|^6047 ≤ (11075867612431/25000000000000 : ℝ)^5023
        have hw : |(203408937/400000000 : ℝ)|=(203408937/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s3_2 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1064909411/2000000000 : ℝ)*x 0 + (5085223529/10000000000 : ℝ)*x 1 + (-1336983061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1064909411/2000000000 : ℝ)^6047 ≤ (46825458979297/100000000000000 : ℝ)^5023 := by
    have hnat : (1064909411 : ℕ)^6047*100000000000000^5023 ≤ 46825458979297^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064909411 2000000000 46825458979297 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085223529/10000000000 : ℝ)^6047 ≤ (22151735770253/50000000000000 : ℝ)^5023 := by
    have hnat : (5085223529 : ℕ)^6047*50000000000000^5023 ≤ 22151735770253^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085223529 10000000000 22151735770253 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1336983061/10000000000 : ℝ)^6047 ≤ (554441841511/6250000000000 : ℝ)^5023 := by
    have hnat : (1336983061 : ℕ)^6047*6250000000000^5023 ≤ 554441841511^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336983061 10000000000 554441841511 6250000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1064909411/2000000000 : ℝ), (5085223529/10000000000 : ℝ), (-1336983061/10000000000 : ℝ)] ![(46825458979297/100000000000000 : ℝ), (22151735770253/50000000000000 : ℝ), (554441841511/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1064909411/2000000000 : ℝ)|^6047 ≤ (46825458979297/100000000000000 : ℝ)^5023
        have hw : |(1064909411/2000000000 : ℝ)|=(1064909411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085223529/10000000000 : ℝ)|^6047 ≤ (22151735770253/50000000000000 : ℝ)^5023
        have hw : |(5085223529/10000000000 : ℝ)|=(5085223529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1336983061/10000000000 : ℝ)|^6047 ≤ (554441841511/6250000000000 : ℝ)^5023
        have hw : |(-1336983061/10000000000 : ℝ)|=(1336983061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s3_3 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1993574393/5000000000 : ℝ)*x 0 + (416473839/1250000000 : ℝ)*x 1 + (4701833913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1993574393/5000000000 : ℝ)^6047 ≤ (33056174751021/100000000000000 : ℝ)^5023 := by
    have hnat : (1993574393 : ℕ)^6047*100000000000000^5023 ≤ 33056174751021^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1993574393 5000000000 33056174751021 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (416473839/1250000000 : ℝ)^6047 ≤ (6657477912471/25000000000000 : ℝ)^5023 := by
    have hnat : (416473839 : ℕ)^6047*25000000000000^5023 ≤ 6657477912471^5023*1250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416473839 1250000000 6657477912471 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4701833913/10000000000 : ℝ)^6047 ≤ (40313913587317/100000000000000 : ℝ)^5023 := by
    have hnat : (4701833913 : ℕ)^6047*100000000000000^5023 ≤ 40313913587317^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4701833913 10000000000 40313913587317 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1993574393/5000000000 : ℝ), (416473839/1250000000 : ℝ), (4701833913/10000000000 : ℝ)] ![(33056174751021/100000000000000 : ℝ), (6657477912471/25000000000000 : ℝ), (40313913587317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1993574393/5000000000 : ℝ)|^6047 ≤ (33056174751021/100000000000000 : ℝ)^5023
        have hw : |(1993574393/5000000000 : ℝ)|=(1993574393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(416473839/1250000000 : ℝ)|^6047 ≤ (6657477912471/25000000000000 : ℝ)^5023
        have hw : |(416473839/1250000000 : ℝ)|=(416473839/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4701833913/10000000000 : ℝ)|^6047 ≤ (40313913587317/100000000000000 : ℝ)^5023
        have hw : |(4701833913/10000000000 : ℝ)|=(4701833913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s3_4 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-283484473/2500000000 : ℝ)*x 0 + (636467171/1250000000 : ℝ)*x 1 + (5340254/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (283484473/2500000000 : ℝ)^6047 ≤ (1818845178337/25000000000000 : ℝ)^5023 := by
    have hnat : (283484473 : ℕ)^6047*25000000000000^5023 ≤ 1818845178337^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283484473 2500000000 1818845178337 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636467171/1250000000 : ℝ)^6047 ≤ (44371799460831/100000000000000 : ℝ)^5023 := by
    have hnat : (636467171 : ℕ)^6047*100000000000000^5023 ≤ 44371799460831^5023*1250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636467171 1250000000 44371799460831 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5340254/9765625 : ℝ)^6047 ≤ (48352819805121/100000000000000 : ℝ)^5023 := by
    have hnat : (5340254 : ℕ)^6047*100000000000000^5023 ≤ 48352819805121^5023*9765625^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5340254 9765625 48352819805121 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-283484473/2500000000 : ℝ), (636467171/1250000000 : ℝ), (5340254/9765625 : ℝ)] ![(1818845178337/25000000000000 : ℝ), (44371799460831/100000000000000 : ℝ), (48352819805121/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-283484473/2500000000 : ℝ)|^6047 ≤ (1818845178337/25000000000000 : ℝ)^5023
        have hw : |(-283484473/2500000000 : ℝ)|=(283484473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636467171/1250000000 : ℝ)|^6047 ≤ (44371799460831/100000000000000 : ℝ)^5023
        have hw : |(636467171/1250000000 : ℝ)|=(636467171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5340254/9765625 : ℝ)|^6047 ≤ (48352819805121/100000000000000 : ℝ)^5023
        have hw : |(5340254/9765625 : ℝ)|=(5340254/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s3_5 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5221792111/10000000000 : ℝ)*x 0 + (-190757219/2000000000 : ℝ)*x 1 + (5468420219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5221792111/10000000000 : ℝ)^6047 ≤ (9147947051953/20000000000000 : ℝ)^5023 := by
    have hnat : (5221792111 : ℕ)^6047*20000000000000^5023 ≤ 9147947051953^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221792111 10000000000 9147947051953 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190757219/2000000000 : ℝ)^6047 ≤ (5907443616341/100000000000000 : ℝ)^5023 := by
    have hnat : (190757219 : ℕ)^6047*100000000000000^5023 ≤ 5907443616341^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190757219 2000000000 5907443616341 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468420219/10000000000 : ℝ)^6047 ≤ (48352821114429/100000000000000 : ℝ)^5023 := by
    have hnat : (5468420219 : ℕ)^6047*100000000000000^5023 ≤ 48352821114429^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468420219 10000000000 48352821114429 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5221792111/10000000000 : ℝ), (-190757219/2000000000 : ℝ), (5468420219/10000000000 : ℝ)] ![(9147947051953/20000000000000 : ℝ), (5907443616341/100000000000000 : ℝ), (48352821114429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5221792111/10000000000 : ℝ)|^6047 ≤ (9147947051953/20000000000000 : ℝ)^5023
        have hw : |(5221792111/10000000000 : ℝ)|=(5221792111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-190757219/2000000000 : ℝ)|^6047 ≤ (5907443616341/100000000000000 : ℝ)^5023
        have hw : |(-190757219/2000000000 : ℝ)|=(190757219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468420219/10000000000 : ℝ)|^6047 ≤ (48352821114429/100000000000000 : ℝ)^5023
        have hw : |(5468420219/10000000000 : ℝ)|=(5468420219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s3_6 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5221792331/10000000000 : ℝ)*x 0 + (5468419871/10000000000 : ℝ)*x 1 + (-23844657/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5221792331/10000000000 : ℝ)^6047 ≤ (5717467197461/12500000000000 : ℝ)^5023 := by
    have hnat : (5221792331 : ℕ)^6047*12500000000000^5023 ≤ 5717467197461^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221792331 10000000000 5717467197461 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468419871/10000000000 : ℝ)^6047 ≤ (9670563482009/20000000000000 : ℝ)^5023 := by
    have hnat : (5468419871 : ℕ)^6047*20000000000000^5023 ≤ 9670563482009^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468419871 10000000000 9670563482009 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (23844657/250000000 : ℝ)^6047 ≤ (5907444995763/100000000000000 : ℝ)^5023 := by
    have hnat : (23844657 : ℕ)^6047*100000000000000^5023 ≤ 5907444995763^5023*250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23844657 250000000 5907444995763 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5221792331/10000000000 : ℝ), (5468419871/10000000000 : ℝ), (-23844657/250000000 : ℝ)] ![(5717467197461/12500000000000 : ℝ), (9670563482009/20000000000000 : ℝ), (5907444995763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5221792331/10000000000 : ℝ)|^6047 ≤ (5717467197461/12500000000000 : ℝ)^5023
        have hw : |(5221792331/10000000000 : ℝ)|=(5221792331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468419871/10000000000 : ℝ)|^6047 ≤ (9670563482009/20000000000000 : ℝ)^5023
        have hw : |(5468419871/10000000000 : ℝ)|=(5468419871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-23844657/250000000 : ℝ)|^6047 ≤ (5907444995763/100000000000000 : ℝ)^5023
        have hw : |(-23844657/250000000 : ℝ)|=(23844657/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_s3_7 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (797653717/2000000000 : ℝ)*x 0 + (2339469949/5000000000 : ℝ)*x 1 + (83878991/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (797653717/2000000000 : ℝ)^6047 ≤ (33067351601753/100000000000000 : ℝ)^5023 := by
    have hnat : (797653717 : ℕ)^6047*100000000000000^5023 ≤ 33067351601753^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797653717 2000000000 33067351601753 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2339469949/5000000000 : ℝ)^6047 ≤ (40077718669731/100000000000000 : ℝ)^5023 := by
    have hnat : (2339469949 : ℕ)^6047*100000000000000^5023 ≤ 40077718669731^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2339469949 5000000000 40077718669731 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83878991/250000000 : ℝ)^6047 ≤ (13427464861129/50000000000000 : ℝ)^5023 := by
    have hnat : (83878991 : ℕ)^6047*50000000000000^5023 ≤ 13427464861129^5023*250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83878991 250000000 13427464861129 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(797653717/2000000000 : ℝ), (2339469949/5000000000 : ℝ), (83878991/250000000 : ℝ)] ![(33067351601753/100000000000000 : ℝ), (40077718669731/100000000000000 : ℝ), (13427464861129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(797653717/2000000000 : ℝ)|^6047 ≤ (33067351601753/100000000000000 : ℝ)^5023
        have hw : |(797653717/2000000000 : ℝ)|=(797653717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2339469949/5000000000 : ℝ)|^6047 ≤ (40077718669731/100000000000000 : ℝ)^5023
        have hw : |(2339469949/5000000000 : ℝ)|=(2339469949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83878991/250000000 : ℝ)|^6047 ≤ (13427464861129/50000000000000 : ℝ)^5023
        have hw : |(83878991/250000000 : ℝ)|=(83878991/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1767_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1153/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1103/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17649/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17649/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17649/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17649/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17649/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17649/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9223/100000 : ℝ) ^ (6031/1024 : ℝ) ≤ (4003420653261/5000000000000000000 : ℝ) := by
    have hpowers : (9223/100000 : ℝ)^6031 ≤ (4003420653261/5000000000000000000 : ℝ)^1024 := by
      have hnat : (9223 : ℕ)^6031*5000000000000000000^1024 ≤ 4003420653261^1024*100000^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9223 100000 4003420653261 5000000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9223/100000 : ℝ)) (X := (4003420653261/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17649/100000 : ℝ) ^ (6031/1024 : ℝ) ≤ (457463286047289/12500000000000000000 : ℝ) := by
    have hpowers : (17649/100000 : ℝ)^6031 ≤ (457463286047289/12500000000000000000 : ℝ)^1024 := by
      have hnat : (17649 : ℕ)^6031*12500000000000000000^1024 ≤ 457463286047289^1024*100000^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17649 100000 457463286047289 12500000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17649/100000 : ℝ)) (X := (457463286047289/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500004003420653261/2500000000000000000 : ℝ) ≤ (10000002718952097/10000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (2500004003420653261/2500000000000000000 : ℝ)^1024 ≤ (10000002718952097/10000000000000000 : ℝ)^6031 := by
      have hnat : (2500004003420653261 : ℕ)^1024*10000000000000000^6031 ≤ 10000002718952097^6031*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500004003420653261 2500000000000000000 10000002718952097 10000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002718952097/10000000000000000 : ℝ)) (X := (2500004003420653261/2500000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25000934943675360883/25000000000000000000 : ℝ) ≤ (10000063496432533/10000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (25000934943675360883/25000000000000000000 : ℝ)^1024 ≤ (10000063496432533/10000000000000000 : ℝ)^6031 := by
      have hnat : (25000934943675360883 : ℕ)^1024*10000000000000000^6031 ≤ 10000063496432533^6031*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000934943675360883 25000000000000000000 10000063496432533 10000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000063496432533/10000000000000000 : ℝ)) (X := (25000934943675360883/25000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6250457463286047289/6250000000000000000 : ℝ) ≤ (10000124273912969/10000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (6250457463286047289/6250000000000000000 : ℝ)^1024 ≤ (10000124273912969/10000000000000000 : ℝ)^6031 := by
      have hnat : (6250457463286047289 : ℕ)^1024*10000000000000000^6031 ≤ 10000124273912969^6031*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250457463286047289 6250000000000000000 10000124273912969 10000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000124273912969/10000000000000000 : ℝ)) (X := (6250457463286047289/6250000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4003420653261/5000000000000000000 : ℝ) ≤ ((42129450904243123433/42130000000000000000 : ℝ)+2*(15194370109/210650000000000 : ℝ)*(9223/100000 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (42129450904243123433/42130000000000000000 : ℝ)+2*(15194370109/210650000000000 : ℝ)*(9223/100000 : ℝ)=(10000002718952097/10000000000000000 : ℝ) by norm_num, show 1+2*(4003420653261/5000000000000000000 : ℝ)=(2500004003420653261/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(457463286047289/12500000000000000000 : ℝ)+(4003420653261/5000000000000000000 : ℝ) ≤ ((42129450904243123433/42130000000000000000 : ℝ)+(15194370109/210650000000000 : ℝ)*((17649/100000 : ℝ)+(9223/100000 : ℝ)))^(6031/1024 : ℝ) := by
    rw [show (42129450904243123433/42130000000000000000 : ℝ)+(15194370109/210650000000000 : ℝ)*((17649/100000 : ℝ)+(9223/100000 : ℝ))=(10000063496432533/10000000000000000 : ℝ) by norm_num, show 1+(457463286047289/12500000000000000000 : ℝ)+(4003420653261/5000000000000000000 : ℝ)=(25000934943675360883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(457463286047289/12500000000000000000 : ℝ) ≤ ((42129450904243123433/42130000000000000000 : ℝ)+2*(15194370109/210650000000000 : ℝ)*(17649/100000 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (42129450904243123433/42130000000000000000 : ℝ)+2*(15194370109/210650000000000 : ℝ)*(17649/100000 : ℝ)=(10000124273912969/10000000000000000 : ℝ) by norm_num, show 1+2*(457463286047289/12500000000000000000 : ℝ)=(6250457463286047289/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (42129450904243123433/42130000000000000000 : ℝ)*(X 1 0+X 2 0)+(15194370109/210650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (9223/100000 : ℝ)) (hi := (17649/100000 : ℝ)) (c := (42129450904243123433/42130000000000000000 : ℝ)) (alpha := (15194370109/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (42129450904243123433/42130000000000000000 : ℝ)*(X 0 1+X 2 1)+(15194370109/210650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (9223/100000 : ℝ)) (hi := (17649/100000 : ℝ)) (c := (42129450904243123433/42130000000000000000 : ℝ)) (alpha := (15194370109/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (42129450904243123433/42130000000000000000 : ℝ)*(X 0 2+X 1 2)+(15194370109/210650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (9223/100000 : ℝ)) (hi := (17649/100000 : ℝ)) (c := (42129450904243123433/42130000000000000000 : ℝ)) (alpha := (15194370109/210650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-283404847/2500000000 : ℝ)*X 0 0+(273753473/500000000 : ℝ)*X 0 1+(5085223357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5324547687/10000000000 : ℝ)*X 1 0+(-33424559/250000000 : ℝ)*X 1 1+(203408937/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1064909411/2000000000 : ℝ)*X 2 0+(5085223529/10000000000 : ℝ)*X 2 1+(-1336983061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1993574393/5000000000 : ℝ)*X 0 0+(416473839/1250000000 : ℝ)*X 0 1+(4701833913/10000000000 : ℝ)*X 0 2+(1993574393/5000000000 : ℝ)*X 1 0+(416473839/1250000000 : ℝ)*X 1 1+(4701833913/10000000000 : ℝ)*X 1 2+(1993574393/5000000000 : ℝ)*X 2 0+(416473839/1250000000 : ℝ)*X 2 1+(4701833913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-283484473/2500000000 : ℝ)*X 0 0+(636467171/1250000000 : ℝ)*X 0 1+(5340254/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5221792111/10000000000 : ℝ)*X 1 0+(-190757219/2000000000 : ℝ)*X 1 1+(5468420219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5221792331/10000000000 : ℝ)*X 2 0+(5468419871/10000000000 : ℝ)*X 2 1+(-23844657/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((797653717/2000000000 : ℝ)*X 0 0+(2339469949/5000000000 : ℝ)*X 0 1+(83878991/250000000 : ℝ)*X 0 2+(797653717/2000000000 : ℝ)*X 1 0+(2339469949/5000000000 : ℝ)*X 1 1+(83878991/250000000 : ℝ)*X 1 2+(797653717/2000000000 : ℝ)*X 2 0+(2339469949/5000000000 : ℝ)*X 2 1+(83878991/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (176695133836060215883416267/47875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (569500089/100000000000000 : ℝ)*(base19) + (12078927/5000000000000 : ℝ)*(base23) + (27983863/100000000000000 : ℝ)*(upper2) + (594847/800000000000 : ℝ)*(upper3) + (823759426144963/50000000000000 : ℝ)*(major0) + (823759426144963/50000000000000 : ℝ)*(major1) + (823759426144963/50000000000000 : ℝ)*(major2) + (64128068240871/2500000000000 : ℝ)*(sp0) + (80160249349091/3125000000000 : ℝ)*(sp1) + (641281092118949/25000000000000 : ℝ)*(sp2) + (729906462524187/100000000000000 : ℝ)*(sp3) + (5819036161/100000000000000 : ℝ)*(sp4) + (787723333/20000000000000 : ℝ)*(sp6) + (80323729/3125000000000 : ℝ)*(sp7) + (145981806576703/20000000000000 : ℝ)*(f.failure) + (2565128548671001/100000000000000 : ℝ)*(f.sum) + (4501935816481/957500000000000000000000000 : ℝ)*base66 + (328985224111852911/191500000000000000000000000000000 : ℝ)*base68 + (936800160221647089/191500000000000000000000000000000 : ℝ)*base69 + (1006839319516852911/191500000000000000000000000000000 : ℝ)*base72 + (83235801433/478750000000000000000000000 : ℝ)*base74 + (436056496334352911/191500000000000000000000000000000 : ℝ)*base76 + (395781270733352911/191500000000000000000000000000000 : ℝ)*base78 + (842397423278352911/191500000000000000000000000000000 : ℝ)*base80 + (5034570985063/1915000000000000000000000000 : ℝ)*base81 + (13311623/2000000000000000000000 : ℝ)*base89 + (13311623/2000000000000000000000 : ℝ)*base91 + (13311623/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7376760971743453488879471/2633125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (153965693/50000000000000 : ℝ)*(base19) + (49060103/12500000000000 : ℝ)*(base23) + (39900587/50000000000000 : ℝ)*(lower1) + (27791277/100000000000000 : ℝ)*(upper3) + (613763/20000000000000 : ℝ)*(lower4) + (34418873/50000000000000 : ℝ)*(upper5) + (2131352805993/125000000000 : ℝ)*(major0) + (2131352805993/125000000000 : ℝ)*(major1) + (2131352805993/125000000000 : ℝ)*(major2) + (26341953/1562500000000 : ℝ)*(sp1) + (2654752747618753/100000000000000 : ℝ)*(sp4) + (1327375376901187/50000000000000 : ℝ)*(sp5) + (2654752355137929/100000000000000 : ℝ)*(sp6) + (75541164858593/10000000000000 : ℝ)*(sp7) + (75541164858593/10000000000000 : ℝ)*(f.failure) + (2654752747618753/100000000000000 : ℝ)*(f.sum) + (4633871549911/2106500000000000000000000000 : ℝ)*base66 + (2538647876152821/478750000000000000000000000000 : ℝ)*base68 + (4726453147967821/478750000000000000000000000000 : ℝ)*base70 + (399256230642821/478750000000000000000000000000 : ℝ)*base72 + (54440081947/421300000000000000000000000 : ℝ)*base73 + (529959116085321/478750000000000000000000000000 : ℝ)*base76 + (1161204799671571/478750000000000000000000000000 : ℝ)*base78 + (3602298746234071/478750000000000000000000000000 : ℝ)*base80 + (124795954821/21065000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (6646887/1000000000000000000000 : ℝ)*base90 + (6646887/1000000000000000000000 : ℝ)*base92 + (6646887/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1767_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1153/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1103/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1767_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1767_box_0 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-773162029/10000000000 : ℝ)*x 0 + (5407582999/10000000000 : ℝ)*x 1 + (1081516669/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (773162029/10000000000 : ℝ)^6047 ≤ (229403936383/5000000000000 : ℝ)^5023 := by
    have hnat : (773162029 : ℕ)^6047*5000000000000^5023 ≤ 229403936383^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773162029 10000000000 229403936383 5000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407582999/10000000000 : ℝ)^6047 ≤ (47705958793729/100000000000000 : ℝ)^5023 := by
    have hnat : (5407582999 : ℕ)^6047*100000000000000^5023 ≤ 47705958793729^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407582999 10000000000 47705958793729 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081516669/2000000000 : ℝ)^6047 ≤ (47705962468433/100000000000000 : ℝ)^5023 := by
    have hnat : (1081516669 : ℕ)^6047*100000000000000^5023 ≤ 47705962468433^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081516669 2000000000 47705962468433 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-773162029/10000000000 : ℝ), (5407582999/10000000000 : ℝ), (1081516669/2000000000 : ℝ)] ![(229403936383/5000000000000 : ℝ), (47705958793729/100000000000000 : ℝ), (47705962468433/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-773162029/10000000000 : ℝ)|^6047 ≤ (229403936383/5000000000000 : ℝ)^5023
        have hw : |(-773162029/10000000000 : ℝ)|=(773162029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407582999/10000000000 : ℝ)|^6047 ≤ (47705958793729/100000000000000 : ℝ)^5023
        have hw : |(5407582999/10000000000 : ℝ)|=(5407582999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081516669/2000000000 : ℝ)|^6047 ≤ (47705962468433/100000000000000 : ℝ)^5023
        have hw : |(1081516669/2000000000 : ℝ)|=(1081516669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_1 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (649036249/1250000000 : ℝ)*x 0 + (-540288867/5000000000 : ℝ)*x 1 + (5407583123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (649036249/1250000000 : ℝ)^6047 ≤ (45428811783159/100000000000000 : ℝ)^5023 := by
    have hnat : (649036249 : ℕ)^6047*100000000000000^5023 ≤ 45428811783159^5023*1250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      649036249 1250000000 45428811783159 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540288867/5000000000 : ℝ)^6047 ≤ (6865228092079/100000000000000 : ℝ)^5023 := by
    have hnat : (540288867 : ℕ)^6047*100000000000000^5023 ≤ 6865228092079^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540288867 5000000000 6865228092079 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407583123/10000000000 : ℝ)^6047 ≤ (1908238404427/4000000000000 : ℝ)^5023 := by
    have hnat : (5407583123 : ℕ)^6047*4000000000000^5023 ≤ 1908238404427^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407583123 10000000000 1908238404427 4000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(649036249/1250000000 : ℝ), (-540288867/5000000000 : ℝ), (5407583123/10000000000 : ℝ)] ![(45428811783159/100000000000000 : ℝ), (6865228092079/100000000000000 : ℝ), (1908238404427/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(649036249/1250000000 : ℝ)|^6047 ≤ (45428811783159/100000000000000 : ℝ)^5023
        have hw : |(649036249/1250000000 : ℝ)|=(649036249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-540288867/5000000000 : ℝ)|^6047 ≤ (6865228092079/100000000000000 : ℝ)^5023
        have hw : |(-540288867/5000000000 : ℝ)|=(540288867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407583123/10000000000 : ℝ)|^6047 ≤ (1908238404427/4000000000000 : ℝ)^5023
        have hw : |(5407583123/10000000000 : ℝ)|=(5407583123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_2 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5192289637/10000000000 : ℝ)*x 0 + (84493491/156250000 : ℝ)*x 1 + (-216115561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5192289637/10000000000 : ℝ)^6047 ≤ (45428808043969/100000000000000 : ℝ)^5023 := by
    have hnat : (5192289637 : ℕ)^6047*100000000000000^5023 ≤ 45428808043969^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192289637 10000000000 45428808043969 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84493491/156250000 : ℝ)^6047 ≤ (23852981653727/50000000000000 : ℝ)^5023 := by
    have hnat : (84493491 : ℕ)^6047*50000000000000^5023 ≤ 23852981653727^5023*156250000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84493491 156250000 23852981653727 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216115561/2000000000 : ℝ)^6047 ≤ (3432614317561/50000000000000 : ℝ)^5023 := by
    have hnat : (216115561 : ℕ)^6047*50000000000000^5023 ≤ 3432614317561^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216115561 2000000000 3432614317561 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5192289637/10000000000 : ℝ), (84493491/156250000 : ℝ), (-216115561/2000000000 : ℝ)] ![(45428808043969/100000000000000 : ℝ), (23852981653727/50000000000000 : ℝ), (3432614317561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5192289637/10000000000 : ℝ)|^6047 ≤ (45428808043969/100000000000000 : ℝ)^5023
        have hw : |(5192289637/10000000000 : ℝ)|=(5192289637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84493491/156250000 : ℝ)|^6047 ≤ (23852981653727/50000000000000 : ℝ)^5023
        have hw : |(84493491/156250000 : ℝ)|=(84493491/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-216115561/2000000000 : ℝ)|^6047 ≤ (3432614317561/50000000000000 : ℝ)^5023
        have hw : |(-216115561/2000000000 : ℝ)|=(216115561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_3 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2255528727/5000000000 : ℝ)*x 0 + (940535247/2500000000 : ℝ)*x 1 + (3762140891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2255528727/5000000000 : ℝ)^6047 ≤ (7670589965609/20000000000000 : ℝ)^5023 := by
    have hnat : (2255528727 : ℕ)^6047*20000000000000^5023 ≤ 7670589965609^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255528727 5000000000 7670589965609 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (940535247/2500000000 : ℝ)^6047 ≤ (30823525556633/100000000000000 : ℝ)^5023 := by
    have hnat : (940535247 : ℕ)^6047*100000000000000^5023 ≤ 30823525556633^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940535247 2500000000 30823525556633 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3762140891/10000000000 : ℝ)^6047 ≤ (30823524599889/100000000000000 : ℝ)^5023 := by
    have hnat : (3762140891 : ℕ)^6047*100000000000000^5023 ≤ 30823524599889^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3762140891 10000000000 30823524599889 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2255528727/5000000000 : ℝ), (940535247/2500000000 : ℝ), (3762140891/10000000000 : ℝ)] ![(7670589965609/20000000000000 : ℝ), (30823525556633/100000000000000 : ℝ), (30823524599889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2255528727/5000000000 : ℝ)|^6047 ≤ (7670589965609/20000000000000 : ℝ)^5023
        have hw : |(2255528727/5000000000 : ℝ)|=(2255528727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(940535247/2500000000 : ℝ)|^6047 ≤ (30823525556633/100000000000000 : ℝ)^5023
        have hw : |(940535247/2500000000 : ℝ)|=(940535247/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3762140891/10000000000 : ℝ)|^6047 ≤ (30823524599889/100000000000000 : ℝ)^5023
        have hw : |(3762140891/10000000000 : ℝ)|=(3762140891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_4 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-12261129/80000000 : ℝ)*x 0 + (1282459/2500000 : ℝ)*x 1 + (5129835679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (12261129/80000000 : ℝ)^6047 ≤ (5228204357191/50000000000000 : ℝ)^5023 := by
    have hnat : (12261129 : ℕ)^6047*50000000000000^5023 ≤ 5228204357191^5023*80000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12261129 80000000 5228204357191 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1282459/2500000 : ℝ)^6047 ≤ (179087189297/400000000000 : ℝ)^5023 := by
    have hnat : (1282459 : ℕ)^6047*400000000000^5023 ≤ 179087189297^5023*2500000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1282459 2500000 179087189297 400000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5129835679/10000000000 : ℝ)^6047 ≤ (4477179395151/10000000000000 : ℝ)^5023 := by
    have hnat : (5129835679 : ℕ)^6047*10000000000000^5023 ≤ 4477179395151^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5129835679 10000000000 4477179395151 10000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-12261129/80000000 : ℝ), (1282459/2500000 : ℝ), (5129835679/10000000000 : ℝ)] ![(5228204357191/50000000000000 : ℝ), (179087189297/400000000000 : ℝ), (4477179395151/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-12261129/80000000 : ℝ)|^6047 ≤ (5228204357191/50000000000000 : ℝ)^5023
        have hw : |(-12261129/80000000 : ℝ)|=(12261129/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1282459/2500000 : ℝ)|^6047 ≤ (179087189297/400000000000 : ℝ)^5023
        have hw : |(1282459/2500000 : ℝ)|=(1282459/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5129835679/10000000000 : ℝ)|^6047 ≤ (4477179395151/10000000000000 : ℝ)^5023
        have hw : |(5129835679/10000000000 : ℝ)|=(5129835679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_5 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5376926821/10000000000 : ℝ)*x 0 + (-241509581/2000000000 : ℝ)*x 1 + (2564917783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5376926821/10000000000 : ℝ)^6047 ≤ (47380562335059/100000000000000 : ℝ)^5023 := by
    have hnat : (5376926821 : ℕ)^6047*100000000000000^5023 ≤ 47380562335059^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376926821 10000000000 47380562335059 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241509581/2000000000 : ℝ)^6047 ≤ (245238902743/3125000000000 : ℝ)^5023 := by
    have hnat : (241509581 : ℕ)^6047*3125000000000^5023 ≤ 245238902743^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241509581 2000000000 245238902743 3125000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2564917783/5000000000 : ℝ)^6047 ≤ (22385896382111/50000000000000 : ℝ)^5023 := by
    have hnat : (2564917783 : ℕ)^6047*50000000000000^5023 ≤ 22385896382111^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2564917783 5000000000 22385896382111 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5376926821/10000000000 : ℝ), (-241509581/2000000000 : ℝ), (2564917783/5000000000 : ℝ)] ![(47380562335059/100000000000000 : ℝ), (245238902743/3125000000000 : ℝ), (22385896382111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5376926821/10000000000 : ℝ)|^6047 ≤ (47380562335059/100000000000000 : ℝ)^5023
        have hw : |(5376926821/10000000000 : ℝ)|=(5376926821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-241509581/2000000000 : ℝ)|^6047 ≤ (245238902743/3125000000000 : ℝ)^5023
        have hw : |(-241509581/2000000000 : ℝ)|=(241509581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2564917783/5000000000 : ℝ)|^6047 ≤ (22385896382111/50000000000000 : ℝ)^5023
        have hw : |(2564917783/5000000000 : ℝ)|=(2564917783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_6 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336057909/625000000 : ℝ)*x 0 + (512983571/1000000000 : ℝ)*x 1 + (-1207548087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336057909/625000000 : ℝ)^6047 ≤ (47380559396579/100000000000000 : ℝ)^5023 := by
    have hnat : (336057909 : ℕ)^6047*100000000000000^5023 ≤ 47380559396579^5023*625000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336057909 625000000 47380559396579 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (512983571/1000000000 : ℝ)^6047 ≤ (44771794277227/100000000000000 : ℝ)^5023 := by
    have hnat : (512983571 : ℕ)^6047*100000000000000^5023 ≤ 44771794277227^5023*1000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512983571 1000000000 44771794277227 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1207548087/10000000000 : ℝ)^6047 ≤ (980955788961/12500000000000 : ℝ)^5023 := by
    have hnat : (1207548087 : ℕ)^6047*12500000000000^5023 ≤ 980955788961^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1207548087 10000000000 980955788961 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336057909/625000000 : ℝ), (512983571/1000000000 : ℝ), (-1207548087/10000000000 : ℝ)] ![(47380559396579/100000000000000 : ℝ), (44771794277227/100000000000000 : ℝ), (980955788961/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336057909/625000000 : ℝ)|^6047 ≤ (47380559396579/100000000000000 : ℝ)^5023
        have hw : |(336057909/625000000 : ℝ)|=(336057909/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(512983571/1000000000 : ℝ)|^6047 ≤ (44771794277227/100000000000000 : ℝ)^5023
        have hw : |(512983571/1000000000 : ℝ)|=(512983571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1207548087/10000000000 : ℝ)|^6047 ≤ (980955788961/12500000000000 : ℝ)^5023
        have hw : |(-1207548087/10000000000 : ℝ)|=(1207548087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_7 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (34237797/100000000 : ℝ)*x 0 + (2151878601/5000000000 : ℝ)*x 1 + (4303756561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34237797/100000000 : ℝ)^6047 ≤ (27517509671897/100000000000000 : ℝ)^5023 := by
    have hnat : (34237797 : ℕ)^6047*100000000000000^5023 ≤ 27517509671897^5023*100000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34237797 100000000 27517509671897 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2151878601/5000000000 : ℝ)^6047 ≤ (36241248405673/100000000000000 : ℝ)^5023 := by
    have hnat : (2151878601 : ℕ)^6047*100000000000000^5023 ≤ 36241248405673^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151878601 5000000000 36241248405673 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4303756561/10000000000 : ℝ)^6047 ≤ (9060310476879/25000000000000 : ℝ)^5023 := by
    have hnat : (4303756561 : ℕ)^6047*25000000000000^5023 ≤ 9060310476879^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4303756561 10000000000 9060310476879 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34237797/100000000 : ℝ), (2151878601/5000000000 : ℝ), (4303756561/10000000000 : ℝ)] ![(27517509671897/100000000000000 : ℝ), (36241248405673/100000000000000 : ℝ), (9060310476879/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34237797/100000000 : ℝ)|^6047 ≤ (27517509671897/100000000000000 : ℝ)^5023
        have hw : |(34237797/100000000 : ℝ)|=(34237797/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2151878601/5000000000 : ℝ)|^6047 ≤ (36241248405673/100000000000000 : ℝ)^5023
        have hw : |(2151878601/5000000000 : ℝ)|=(2151878601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4303756561/10000000000 : ℝ)|^6047 ≤ (9060310476879/25000000000000 : ℝ)^5023
        have hw : |(4303756561/10000000000 : ℝ)|=(4303756561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_8 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-683559373/5000000000 : ℝ)*x 0 + (1229184591/2500000000 : ℝ)*x 1 + (1093542559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (683559373/5000000000 : ℝ)^6047 ≤ (2278084223747/25000000000000 : ℝ)^5023 := by
    have hnat : (683559373 : ℕ)^6047*25000000000000^5023 ≤ 2278084223747^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683559373 5000000000 2278084223747 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1229184591/2500000000 : ℝ)^6047 ≤ (2127118611913/5000000000000 : ℝ)^5023 := by
    have hnat : (1229184591 : ℕ)^6047*5000000000000^5023 ≤ 2127118611913^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229184591 2500000000 2127118611913 5000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1093542559/2000000000 : ℝ)^6047 ≤ (4834529084023/10000000000000 : ℝ)^5023 := by
    have hnat : (1093542559 : ℕ)^6047*10000000000000^5023 ≤ 4834529084023^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093542559 2000000000 4834529084023 10000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-683559373/5000000000 : ℝ), (1229184591/2500000000 : ℝ), (1093542559/2000000000 : ℝ)] ![(2278084223747/25000000000000 : ℝ), (2127118611913/5000000000000 : ℝ), (4834529084023/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-683559373/5000000000 : ℝ)|^6047 ≤ (2278084223747/25000000000000 : ℝ)^5023
        have hw : |(-683559373/5000000000 : ℝ)|=(683559373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1229184591/2500000000 : ℝ)|^6047 ≤ (2127118611913/5000000000000 : ℝ)^5023
        have hw : |(1229184591/2500000000 : ℝ)|=(1229184591/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1093542559/2000000000 : ℝ)|^6047 ≤ (4834529084023/10000000000000 : ℝ)^5023
        have hw : |(1093542559/2000000000 : ℝ)|=(1093542559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_9 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5152398013/10000000000 : ℝ)*x 0 + (-1051803681/10000000000 : ℝ)*x 1 + (5467712367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5152398013/10000000000 : ℝ)^6047 ≤ (11252240514901/25000000000000 : ℝ)^5023 := by
    have hnat : (5152398013 : ℕ)^6047*25000000000000^5023 ≤ 11252240514901^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152398013 10000000000 11252240514901 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051803681/10000000000 : ℝ)^6047 ≤ (6645751635367/100000000000000 : ℝ)^5023 := by
    have hnat : (1051803681 : ℕ)^6047*100000000000000^5023 ≤ 6645751635367^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051803681 10000000000 6645751635367 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5467712367/10000000000 : ℝ)^6047 ≤ (1510790196387/3125000000000 : ℝ)^5023 := by
    have hnat : (5467712367 : ℕ)^6047*3125000000000^5023 ≤ 1510790196387^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467712367 10000000000 1510790196387 3125000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5152398013/10000000000 : ℝ), (-1051803681/10000000000 : ℝ), (5467712367/10000000000 : ℝ)] ![(11252240514901/25000000000000 : ℝ), (6645751635367/100000000000000 : ℝ), (1510790196387/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5152398013/10000000000 : ℝ)|^6047 ≤ (11252240514901/25000000000000 : ℝ)^5023
        have hw : |(5152398013/10000000000 : ℝ)|=(5152398013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1051803681/10000000000 : ℝ)|^6047 ≤ (6645751635367/100000000000000 : ℝ)^5023
        have hw : |(-1051803681/10000000000 : ℝ)|=(1051803681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5467712367/10000000000 : ℝ)|^6047 ≤ (1510790196387/3125000000000 : ℝ)^5023
        have hw : |(5467712367/10000000000 : ℝ)|=(5467712367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_10 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1030479551/2000000000 : ℝ)*x 0 + (5467712529/10000000000 : ℝ)*x 1 + (-1051803811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1030479551/2000000000 : ℝ)^6047 ≤ (45008959346377/100000000000000 : ℝ)^5023 := by
    have hnat : (1030479551 : ℕ)^6047*100000000000000^5023 ≤ 45008959346377^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030479551 2000000000 45008959346377 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5467712529/10000000000 : ℝ)^6047 ≤ (48345288008793/100000000000000 : ℝ)^5023 := by
    have hnat : (5467712529 : ℕ)^6047*100000000000000^5023 ≤ 48345288008793^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5467712529 10000000000 48345288008793 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051803811/10000000000 : ℝ)^6047 ≤ (1329150524843/20000000000000 : ℝ)^5023 := by
    have hnat : (1051803811 : ℕ)^6047*20000000000000^5023 ≤ 1329150524843^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051803811 10000000000 1329150524843 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1030479551/2000000000 : ℝ), (5467712529/10000000000 : ℝ), (-1051803811/10000000000 : ℝ)] ![(45008959346377/100000000000000 : ℝ), (48345288008793/100000000000000 : ℝ), (1329150524843/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1030479551/2000000000 : ℝ)|^6047 ≤ (45008959346377/100000000000000 : ℝ)^5023
        have hw : |(1030479551/2000000000 : ℝ)|=(1030479551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5467712529/10000000000 : ℝ)|^6047 ≤ (48345288008793/100000000000000 : ℝ)^5023
        have hw : |(5467712529/10000000000 : ℝ)|=(5467712529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051803811/10000000000 : ℝ)|^6047 ≤ (1329150524843/20000000000000 : ℝ)^5023
        have hw : |(-1051803811/10000000000 : ℝ)|=(1051803811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_11 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4736026327/10000000000 : ℝ)*x 0 + (1822225489/5000000000 : ℝ)*x 1 + (728890351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4736026327/10000000000 : ℝ)^6047 ≤ (5083388661799/12500000000000 : ℝ)^5023 := by
    have hnat : (4736026327 : ℕ)^6047*12500000000000^5023 ≤ 5083388661799^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4736026327 10000000000 5083388661799 12500000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1822225489/5000000000 : ℝ)^6047 ≤ (370830519191/1250000000000 : ℝ)^5023 := by
    have hnat : (1822225489 : ℕ)^6047*1250000000000^5023 ≤ 370830519191^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822225489 5000000000 370830519191 1250000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (728890351/2000000000 : ℝ)^6047 ≤ (37083061437/125000000000 : ℝ)^5023 := by
    have hnat : (728890351 : ℕ)^6047*125000000000^5023 ≤ 37083061437^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      728890351 2000000000 37083061437 125000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4736026327/10000000000 : ℝ), (1822225489/5000000000 : ℝ), (728890351/2000000000 : ℝ)] ![(5083388661799/12500000000000 : ℝ), (370830519191/1250000000000 : ℝ), (37083061437/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4736026327/10000000000 : ℝ)|^6047 ≤ (5083388661799/12500000000000 : ℝ)^5023
        have hw : |(4736026327/10000000000 : ℝ)|=(4736026327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1822225489/5000000000 : ℝ)|^6047 ≤ (370830519191/1250000000000 : ℝ)^5023
        have hw : |(1822225489/5000000000 : ℝ)|=(1822225489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(728890351/2000000000 : ℝ)|^6047 ≤ (37083061437/125000000000 : ℝ)^5023
        have hw : |(728890351/2000000000 : ℝ)|=(728890351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_12 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-924129113/10000000000 : ℝ)*x 0 + (112176189/200000000 : ℝ)*x 1 + (5100320807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (924129113/10000000000 : ℝ)^6047 ≤ (1421754491699/25000000000000 : ℝ)^5023 := by
    have hnat : (924129113 : ℕ)^6047*25000000000000^5023 ≤ 1421754491699^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924129113 10000000000 1421754491699 25000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112176189/200000000 : ℝ)^6047 ≤ (3115694877157/6250000000000 : ℝ)^5023 := by
    have hnat : (112176189 : ℕ)^6047*6250000000000^5023 ≤ 3115694877157^5023*200000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112176189 200000000 3115694877157 6250000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5100320807/10000000000 : ℝ)^6047 ≤ (8892372796549/20000000000000 : ℝ)^5023 := by
    have hnat : (5100320807 : ℕ)^6047*20000000000000^5023 ≤ 8892372796549^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5100320807 10000000000 8892372796549 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-924129113/10000000000 : ℝ), (112176189/200000000 : ℝ), (5100320807/10000000000 : ℝ)] ![(1421754491699/25000000000000 : ℝ), (3115694877157/6250000000000 : ℝ), (8892372796549/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-924129113/10000000000 : ℝ)|^6047 ≤ (1421754491699/25000000000000 : ℝ)^5023
        have hw : |(-924129113/10000000000 : ℝ)|=(924129113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112176189/200000000 : ℝ)|^6047 ≤ (3115694877157/6250000000000 : ℝ)^5023
        have hw : |(112176189/200000000 : ℝ)|=(112176189/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5100320807/10000000000 : ℝ)|^6047 ≤ (8892372796549/20000000000000 : ℝ)^5023
        have hw : |(5100320807/10000000000 : ℝ)|=(5100320807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_13 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5396623569/10000000000 : ℝ)*x 0 + (-1220432003/10000000000 : ℝ)*x 1 + (510032011/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5396623569/10000000000 : ℝ)^6047 ≤ (47589587887211/100000000000000 : ℝ)^5023 := by
    have hnat : (5396623569 : ℕ)^6047*100000000000000^5023 ≤ 47589587887211^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396623569 10000000000 47589587887211 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1220432003/10000000000 : ℝ)^6047 ≤ (3974277712979/50000000000000 : ℝ)^5023 := by
    have hnat : (1220432003 : ℕ)^6047*50000000000000^5023 ≤ 3974277712979^5023*10000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220432003 10000000000 3974277712979 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510032011/1000000000 : ℝ)^6047 ≤ (4446185666799/10000000000000 : ℝ)^5023 := by
    have hnat : (510032011 : ℕ)^6047*10000000000000^5023 ≤ 4446185666799^5023*1000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510032011 1000000000 4446185666799 10000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5396623569/10000000000 : ℝ), (-1220432003/10000000000 : ℝ), (510032011/1000000000 : ℝ)] ![(47589587887211/100000000000000 : ℝ), (3974277712979/50000000000000 : ℝ), (4446185666799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5396623569/10000000000 : ℝ)|^6047 ≤ (47589587887211/100000000000000 : ℝ)^5023
        have hw : |(5396623569/10000000000 : ℝ)|=(5396623569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1220432003/10000000000 : ℝ)|^6047 ≤ (3974277712979/50000000000000 : ℝ)^5023
        have hw : |(-1220432003/10000000000 : ℝ)|=(1220432003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(510032011/1000000000 : ℝ)|^6047 ≤ (4446185666799/10000000000000 : ℝ)^5023
        have hw : |(510032011/1000000000 : ℝ)|=(510032011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_14 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (539662251/1000000000 : ℝ)*x 0 + (1275080139/2500000000 : ℝ)*x 1 + (-30510821/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (539662251/1000000000 : ℝ)^6047 ≤ (47589576644719/100000000000000 : ℝ)^5023 := by
    have hnat : (539662251 : ℕ)^6047*100000000000000^5023 ≤ 47589576644719^5023*1000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539662251 1000000000 47589576644719 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1275080139/2500000000 : ℝ)^6047 ≤ (22230930674297/50000000000000 : ℝ)^5023 := by
    have hnat : (1275080139 : ℕ)^6047*50000000000000^5023 ≤ 22230930674297^5023*2500000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1275080139 2500000000 22230930674297 50000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30510821/250000000 : ℝ)^6047 ≤ (7948561988573/100000000000000 : ℝ)^5023 := by
    have hnat : (30510821 : ℕ)^6047*100000000000000^5023 ≤ 7948561988573^5023*250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30510821 250000000 7948561988573 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(539662251/1000000000 : ℝ), (1275080139/2500000000 : ℝ), (-30510821/250000000 : ℝ)] ![(47589576644719/100000000000000 : ℝ), (22230930674297/50000000000000 : ℝ), (7948561988573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(539662251/1000000000 : ℝ)|^6047 ≤ (47589576644719/100000000000000 : ℝ)^5023
        have hw : |(539662251/1000000000 : ℝ)|=(539662251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1275080139/2500000000 : ℝ)|^6047 ≤ (22230930674297/50000000000000 : ℝ)^5023
        have hw : |(1275080139/2500000000 : ℝ)|=(1275080139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30510821/250000000 : ℝ)|^6047 ≤ (7948561988573/100000000000000 : ℝ)^5023
        have hw : |(-30510821/250000000 : ℝ)|=(30510821/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1767_box_15 (p : ℝ) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (412882893/1250000000 : ℝ)*x 0 + (872215451/2000000000 : ℝ)*x 1 + (2180539961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412882893/1250000000 : ℝ)^6047 ≤ (5270747258139/20000000000000 : ℝ)^5023 := by
    have hnat : (412882893 : ℕ)^6047*20000000000000^5023 ≤ 5270747258139^5023*1250000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412882893 1250000000 5270747258139 20000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872215451/2000000000 : ℝ)^6047 ≤ (36823118292357/100000000000000 : ℝ)^5023 := by
    have hnat : (872215451 : ℕ)^6047*100000000000000^5023 ≤ 36823118292357^5023*2000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872215451 2000000000 36823118292357 100000000000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2180539961/5000000000 : ℝ)^6047 ≤ (575361646909/1562500000000 : ℝ)^5023 := by
    have hnat : (2180539961 : ℕ)^6047*1562500000000^5023 ≤ 575361646909^5023*5000000000^6047 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180539961 5000000000 575361646909 1562500000000 6047 5023 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6047/1024 : ℝ)) 6047 5023 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(412882893/1250000000 : ℝ), (872215451/2000000000 : ℝ), (2180539961/5000000000 : ℝ)] ![(5270747258139/20000000000000 : ℝ), (36823118292357/100000000000000 : ℝ), (575361646909/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(412882893/1250000000 : ℝ)|^6047 ≤ (5270747258139/20000000000000 : ℝ)^5023
        have hw : |(412882893/1250000000 : ℝ)|=(412882893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(872215451/2000000000 : ℝ)|^6047 ≤ (36823118292357/100000000000000 : ℝ)^5023
        have hw : |(872215451/2000000000 : ℝ)|=(872215451/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2180539961/5000000000 : ℝ)|^6047 ≤ (575361646909/1562500000000 : ℝ)^5023
        have hw : |(2180539961/5000000000 : ℝ)|=(2180539961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1767_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1103/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1153/12500 : ℝ)*pair X i i ≤ pair X i h) :
    -(69251/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58939/100000 : ℝ) ∧ (82499/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (23301/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1103/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1153/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1103/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1153/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1103/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1153/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1103/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1153/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1103/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1153/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1103/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1153/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1153/12500 : ℝ) ^ (6031/1024 : ℝ) ≤ (16023911385159/20000000000000000000 : ℝ) := by
    have hpowers : (1153/12500 : ℝ)^6031 ≤ (16023911385159/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1153 : ℕ)^6031*20000000000000000000^1024 ≤ 16023911385159^1024*12500^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1153 12500 16023911385159 20000000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1153/12500 : ℝ)) (X := (16023911385159/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1103/6250 : ℝ) ^ (6031/1024 : ℝ) ≤ (3658485176823793/100000000000000000000 : ℝ) := by
    have hpowers : (1103/6250 : ℝ)^6031 ≤ (3658485176823793/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1103 : ℕ)^6031*100000000000000000000^1024 ≤ 3658485176823793^1024*6250^6031 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1103 6250 3658485176823793 100000000000000000000 6031 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1103/6250 : ℝ)) (X := (3658485176823793/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000016023911385159/10000000000000000000 : ℝ) ≤ (156250042510763/156250000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (10000016023911385159/10000000000000000000 : ℝ)^1024 ≤ (156250042510763/156250000000000 : ℝ)^6031 := by
      have hnat : (10000016023911385159 : ℕ)^1024*156250000000000^6031 ≤ 156250042510763^6031*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000016023911385159 10000000000000000000 156250042510763 156250000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156250042510763/156250000000000 : ℝ)) (X := (10000016023911385159/10000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25000934651183437397/25000000000000000000 : ℝ) ≤ (2000012695313667/2000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (25000934651183437397/25000000000000000000 : ℝ)^1024 ≤ (2000012695313667/2000000000000000 : ℝ)^6031 := by
      have hnat : (25000934651183437397 : ℕ)^1024*2000000000000000^6031 ≤ 2000012695313667^6031*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000934651183437397 25000000000000000000 2000012695313667 2000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000012695313667/2000000000000000 : ℝ)) (X := (25000934651183437397/25000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003658485176823793/50000000000000000000 : ℝ) ≤ (5000062116223919/5000000000000000 : ℝ) ^ (6031/1024 : ℝ) := by
    have hpowers : (50003658485176823793/50000000000000000000 : ℝ)^1024 ≤ (5000062116223919/5000000000000000 : ℝ)^6031 := by
      have hnat : (50003658485176823793 : ℕ)^1024*5000000000000000^6031 ≤ 5000062116223919^6031*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003658485176823793 50000000000000000000 5000062116223919 5000000000000000 1024 6031 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000062116223919/5000000000000000 : ℝ)) (X := (50003658485176823793/50000000000000000000 : ℝ)) (by norm_num) 6031 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(16023911385159/20000000000000000000 : ℝ) ≤ ((5264931380913603089/5265000000000000000 : ℝ)+2*(60755879503/842400000000000 : ℝ)*(1153/12500 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (5264931380913603089/5265000000000000000 : ℝ)+2*(60755879503/842400000000000 : ℝ)*(1153/12500 : ℝ)=(156250042510763/156250000000000 : ℝ) by norm_num, show 1+2*(16023911385159/20000000000000000000 : ℝ)=(10000016023911385159/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3658485176823793/100000000000000000000 : ℝ)+(16023911385159/20000000000000000000 : ℝ) ≤ ((5264931380913603089/5265000000000000000 : ℝ)+(60755879503/842400000000000 : ℝ)*((1103/6250 : ℝ)+(1153/12500 : ℝ)))^(6031/1024 : ℝ) := by
    rw [show (5264931380913603089/5265000000000000000 : ℝ)+(60755879503/842400000000000 : ℝ)*((1103/6250 : ℝ)+(1153/12500 : ℝ))=(2000012695313667/2000000000000000 : ℝ) by norm_num, show 1+(3658485176823793/100000000000000000000 : ℝ)+(16023911385159/20000000000000000000 : ℝ)=(25000934651183437397/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3658485176823793/100000000000000000000 : ℝ) ≤ ((5264931380913603089/5265000000000000000 : ℝ)+2*(60755879503/842400000000000 : ℝ)*(1103/6250 : ℝ))^(6031/1024 : ℝ) := by
    rw [show (5264931380913603089/5265000000000000000 : ℝ)+2*(60755879503/842400000000000 : ℝ)*(1103/6250 : ℝ)=(5000062116223919/5000000000000000 : ℝ) by norm_num, show 1+2*(3658485176823793/100000000000000000000 : ℝ)=(50003658485176823793/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5264931380913603089/5265000000000000000 : ℝ)*(X 1 0+X 2 0)+(60755879503/842400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (1153/12500 : ℝ)) (hi := (1103/6250 : ℝ)) (c := (5264931380913603089/5265000000000000000 : ℝ)) (alpha := (60755879503/842400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5264931380913603089/5265000000000000000 : ℝ)*(X 0 1+X 2 1)+(60755879503/842400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (1153/12500 : ℝ)) (hi := (1103/6250 : ℝ)) (c := (5264931380913603089/5265000000000000000 : ℝ)) (alpha := (60755879503/842400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5264931380913603089/5265000000000000000 : ℝ)*(X 0 2+X 1 2)+(60755879503/842400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6031/1024 : ℝ)) (lo := (1153/12500 : ℝ)) (hi := (1103/6250 : ℝ)) (c := (5264931380913603089/5265000000000000000 : ℝ)) (alpha := (60755879503/842400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-773162029/10000000000 : ℝ)*X 0 0+(5407582999/10000000000 : ℝ)*X 0 1+(1081516669/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((649036249/1250000000 : ℝ)*X 1 0+(-540288867/5000000000 : ℝ)*X 1 1+(5407583123/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5192289637/10000000000 : ℝ)*X 2 0+(84493491/156250000 : ℝ)*X 2 1+(-216115561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2255528727/5000000000 : ℝ)*X 0 0+(940535247/2500000000 : ℝ)*X 0 1+(3762140891/10000000000 : ℝ)*X 0 2+(2255528727/5000000000 : ℝ)*X 1 0+(940535247/2500000000 : ℝ)*X 1 1+(3762140891/10000000000 : ℝ)*X 1 2+(2255528727/5000000000 : ℝ)*X 2 0+(940535247/2500000000 : ℝ)*X 2 1+(3762140891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-12261129/80000000 : ℝ)*X 0 0+(1282459/2500000 : ℝ)*X 0 1+(5129835679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5376926821/10000000000 : ℝ)*X 1 0+(-241509581/2000000000 : ℝ)*X 1 1+(2564917783/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((336057909/625000000 : ℝ)*X 2 0+(512983571/1000000000 : ℝ)*X 2 1+(-1207548087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((34237797/100000000 : ℝ)*X 0 0+(2151878601/5000000000 : ℝ)*X 0 1+(4303756561/10000000000 : ℝ)*X 0 2+(34237797/100000000 : ℝ)*X 1 0+(2151878601/5000000000 : ℝ)*X 1 1+(4303756561/10000000000 : ℝ)*X 1 2+(34237797/100000000 : ℝ)*X 2 0+(2151878601/5000000000 : ℝ)*X 2 1+(4303756561/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-683559373/5000000000 : ℝ)*X 0 0+(1229184591/2500000000 : ℝ)*X 0 1+(1093542559/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5152398013/10000000000 : ℝ)*X 1 0+(-1051803681/10000000000 : ℝ)*X 1 1+(5467712367/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1030479551/2000000000 : ℝ)*X 2 0+(5467712529/10000000000 : ℝ)*X 2 1+(-1051803811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4736026327/10000000000 : ℝ)*X 0 0+(1822225489/5000000000 : ℝ)*X 0 1+(728890351/2000000000 : ℝ)*X 0 2+(4736026327/10000000000 : ℝ)*X 1 0+(1822225489/5000000000 : ℝ)*X 1 1+(728890351/2000000000 : ℝ)*X 1 2+(4736026327/10000000000 : ℝ)*X 2 0+(1822225489/5000000000 : ℝ)*X 2 1+(728890351/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-924129113/10000000000 : ℝ)*X 0 0+(112176189/200000000 : ℝ)*X 0 1+(5100320807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5396623569/10000000000 : ℝ)*X 1 0+(-1220432003/10000000000 : ℝ)*X 1 1+(510032011/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((539662251/1000000000 : ℝ)*X 2 0+(1275080139/2500000000 : ℝ)*X 2 1+(-30510821/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((412882893/1250000000 : ℝ)*X 0 0+(872215451/2000000000 : ℝ)*X 0 1+(2180539961/5000000000 : ℝ)*X 0 2+(412882893/1250000000 : ℝ)*X 1 0+(872215451/2000000000 : ℝ)*X 1 1+(2180539961/5000000000 : ℝ)*X 1 2+(412882893/1250000000 : ℝ)*X 2 0+(872215451/2000000000 : ℝ)*X 2 1+(2180539961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1767_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-69251/100000 : ℝ) ≤ (-270070681075099516379471929/390000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5676461/100000000000000 : ℝ)*(upper1) + (4847877/12500000000000 : ℝ)*(upper3) + (5680757/25000000000000 : ℝ)*(lower4) + (4558717/12500000000000 : ℝ)*(lower5) + (276918059018031/25000000000000 : ℝ)*(major0) + (276918059018031/25000000000000 : ℝ)*(major1) + (276918059018031/25000000000000 : ℝ)*(major2) + (190300311/10000000000000 : ℝ)*(sp1) + (25586637/5000000000000 : ℝ)*(sp2) + (136339391/50000000000000 : ℝ)*(sp3) + (174768951885777/10000000000000 : ℝ)*(sp4) + (87384380792733/5000000000000 : ℝ)*(sp5) + (174768900712503/10000000000000 : ℝ)*(sp6) + (15335551400067/3125000000000 : ℝ)*(sp7) + (490737917480927/100000000000000 : ℝ)*(f.failure) + (174768951885777/10000000000000 : ℝ)*(f.sum) + (10773925849249/3510000000000000000000000000 : ℝ)*base66 + (12612145929943999/14625000000000000000000000000000 : ℝ)*base68 + (10111851132943999/14625000000000000000000000000000 : ℝ)*base70 + (95027693325943999/14625000000000000000000000000000 : ℝ)*base72 + (2540487561109/3510000000000000000000000000 : ℝ)*base74 + (2539150314556001/14625000000000000000000000000000 : ℝ)*base75 + (10861683644056001/14625000000000000000000000000000 : ℝ)*base77 + (13051759317556001/14625000000000000000000000000000 : ℝ)*base79 + (5404895268829/3510000000000000000000000000 : ℝ)*base82 + (143079207/10000000000000000000000 : ℝ)*base89 + (143079207/10000000000000000000000 : ℝ)*base91 + (143079207/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58939/100000 : ℝ) ≤ (1034424674224617142796456602187/1755000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (40860713/100000000000000 : ℝ)*(upper2) + (43378087/100000000000000 : ℝ)*(upper3) + (2862131/50000000000000 : ℝ)*(upper4) + (1570887/100000000000000 : ℝ)*(upper5) + (24827253257717/2000000000000 : ℝ)*(major0) + (24827253257717/2000000000000 : ℝ)*(major1) + (24827253257717/2000000000000 : ℝ)*(major2) + (95655417480879/5000000000000 : ℝ)*(sp0) + (956554020135673/50000000000000 : ℝ)*(sp1) + (1913109421147173/100000000000000 : ℝ)*(sp2) + (549967497771167/100000000000000 : ℝ)*(sp3) + (1214560391/100000000000000 : ℝ)*(sp6) + (1297718109/50000000000000 : ℝ)*(sp9) + (2286089983/100000000000000 : ℝ)*(sp12) + (549967497771167/100000000000000 : ℝ)*(f.failure) + (478277658926891/25000000000000 : ℝ)*(f.sum) + (20703529493573/4212000000000000000000000000 : ℝ)*base66 + (22340269781625521/3510000000000000000000000000000 : ℝ)*base67 + (9222991175505521/3510000000000000000000000000000 : ℝ)*base69 + (15699980412554479/3510000000000000000000000000000 : ℝ)*base72 + (9666756787567/4212000000000000000000000000 : ℝ)*base73 + (1529000333175521/3510000000000000000000000000000 : ℝ)*base75 + (491436042555521/3510000000000000000000000000000 : ℝ)*base77 + (11083218002294479/3510000000000000000000000000000 : ℝ)*base80 + (107786170397/168480000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (30723047/10000000000000000000000 : ℝ)*base89 + (30723047/10000000000000000000000 : ℝ)*base91 + (30723047/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (82499/100000 : ℝ) ≤ (754117840079319250568096446003/914062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3969413/20000000000000 : ℝ)*(upper0) + (46826169/100000000000000 : ℝ)*(upper2) + (20854091/100000000000000 : ℝ)*(lower3) + (5889909/25000000000000 : ℝ)*(lower5) + (147921498248813/12500000000000 : ℝ)*(major0) + (147921498248813/12500000000000 : ℝ)*(major1) + (147921498248813/12500000000000 : ℝ)*(major2) + (1273004329/100000000000000 : ℝ)*(sp3) + (127158297/20000000000000 : ℝ)*(sp4) + (1814966200556589/100000000000000 : ℝ)*(sp8) + (1814967798388407/100000000000000 : ℝ)*(sp9) + (1814967798388407/100000000000000 : ℝ)*(sp10) + (65534288373741/12500000000000 : ℝ)*(sp11) + (962040333/100000000000000 : ℝ)*(sp12) + (32767223749641/6250000000000 : ℝ)*(f.failure) + (1814967798388407/100000000000000 : ℝ)*(f.sum) + (8073652636171/5265000000000000000000000000 : ℝ)*base66 + (177712316695707631/21937500000000000000000000000000 : ℝ)*base68 + (2415943023167369/21937500000000000000000000000000 : ℝ)*base69 + (29465121111729869/21937500000000000000000000000000 : ℝ)*base71 + (18445184044673/2632500000000000000000000000 : ℝ)*base74 + (88060577718917369/21937500000000000000000000000000 : ℝ)*base75 + (72993706180854869/21937500000000000000000000000000 : ℝ)*base77 + (32559409303854869/21937500000000000000000000000000 : ℝ)*base79 + (32990378481091/5265000000000000000000000000 : ℝ)*base82 + (8165119/625000000000000000000 : ℝ)*base90 + (8165119/625000000000000000000 : ℝ)*base92 + (8165119/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-23301/25000 : ℝ) ≤ (-81784425706094630373929140180369/87750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24206907/25000000000000 : ℝ)*(upper3) + (130909283/50000000000000 : ℝ)*(lower4) + (28535253/25000000000000 : ℝ)*(upper5) + (1243157119539521/100000000000000 : ℝ)*(major0) + (1243157119539521/100000000000000 : ℝ)*(major1) + (1243157119539521/100000000000000 : ℝ)*(major2) + (3717854617/100000000000000 : ℝ)*(sp4) + (82964724657/100000000000000 : ℝ)*(sp5) + (11015816503/10000000000000 : ℝ)*(sp6) + (37730641763/100000000000000 : ℝ)*(sp7) + (7866460896123/400000000000 : ℝ)*(sp12) + (196653597716071/10000000000000 : ℝ)*(sp13) + (1966508783720337/100000000000000 : ℝ)*(sp14) + (110144954959467/20000000000000 : ℝ)*(sp15) + (275381252719549/50000000000000 : ℝ)*(f.failure) + (1966618941885367/100000000000000 : ℝ)*(f.sum) + (141596778792263/42120000000000000000000000000 : ℝ)*base65 + (251191815531808627/175500000000000000000000000000000 : ℝ)*base68 + (909179584184308627/175500000000000000000000000000000 : ℝ)*base70 + (365815346330191373/175500000000000000000000000000000 : ℝ)*base71 + (73382158394257/42120000000000000000000000000 : ℝ)*base74 + (49693839356191373/175500000000000000000000000000000 : ℝ)*base75 + (23863634403691373/175500000000000000000000000000000 : ℝ)*base77 + (243688494782191373/175500000000000000000000000000000 : ℝ)*base79 + (31517127054697/42120000000000000000000000000 : ℝ)*base82 + (54234091/5000000000000000000000 : ℝ)*base90 + (54234091/5000000000000000000000 : ℝ)*base92 + (54234091/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1767_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1103/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1153/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58939/100000 : ℝ) else (82499/100000 : ℝ) ≤ X j i ∧ X j i ≤ (23301/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1767_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1767_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58939/100000 : ℝ) else (82499/100000 : ℝ) ≤ X j i ∧ X j i ≤ (23301/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1767_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1767_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6031/1024 : ℝ) ≤ p) (hpb : p ≤ (6047/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (225715641/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17649/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(69251/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(58939/100000 : ℝ) else (82499/100000 : ℝ) ≤ X j i ∧ X j i ≤ (23301/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1767_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
