-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1085_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:54:52.51999+00:00
-- url     : https://prove2.me/submissions/974588ff-cc3b-433f-9041-b11662339d57

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
theorem support_rectangle_w1085_s3_0 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189960619/10000000000 : ℝ)*x 0 + (5435348061/10000000000 : ℝ)*x 1 + (209056279/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189960619/10000000000 : ℝ)^4139 ≤ (265856110359/2000000000000 : ℝ)^3115 := by
    have hnat : (2189960619 : ℕ)^4139*2000000000000^3115 ≤ 265856110359^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189960619 10000000000 265856110359 2000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435348061/10000000000 : ℝ)^4139 ≤ (22241196146823/50000000000000 : ℝ)^3115 := by
    have hnat : (5435348061 : ℕ)^4139*50000000000000^3115 ≤ 22241196146823^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435348061 10000000000 22241196146823 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209056279/400000000 : ℝ)^4139 ≤ (42224802174003/100000000000000 : ℝ)^3115 := by
    have hnat : (209056279 : ℕ)^4139*100000000000000^3115 ≤ 42224802174003^3115*400000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209056279 400000000 42224802174003 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189960619/10000000000 : ℝ), (5435348061/10000000000 : ℝ), (209056279/400000000 : ℝ)] ![(265856110359/2000000000000 : ℝ), (22241196146823/50000000000000 : ℝ), (42224802174003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189960619/10000000000 : ℝ)|^4139 ≤ (265856110359/2000000000000 : ℝ)^3115
        have hw : |(-2189960619/10000000000 : ℝ)|=(2189960619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435348061/10000000000 : ℝ)|^4139 ≤ (22241196146823/50000000000000 : ℝ)^3115
        have hw : |(5435348061/10000000000 : ℝ)|=(5435348061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209056279/400000000 : ℝ)|^4139 ≤ (42224802174003/100000000000000 : ℝ)^3115
        have hw : |(209056279/400000000 : ℝ)|=(209056279/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s3_1 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669400541/1250000000 : ℝ)*x 0 + (-459380997/2000000000 : ℝ)*x 1 + (5226406937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669400541/1250000000 : ℝ)^4139 ≤ (4361301078447/10000000000000 : ℝ)^3115 := by
    have hnat : (669400541 : ℕ)^4139*10000000000000^3115 ≤ 4361301078447^3115*1250000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669400541 1250000000 4361301078447 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (459380997/2000000000 : ℝ)^4139 ≤ (14162187432911/100000000000000 : ℝ)^3115 := by
    have hnat : (459380997 : ℕ)^4139*100000000000000^3115 ≤ 14162187432911^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459380997 2000000000 14162187432911 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5226406937/10000000000 : ℝ)^4139 ≤ (42224801766073/100000000000000 : ℝ)^3115 := by
    have hnat : (5226406937 : ℕ)^4139*100000000000000^3115 ≤ 42224801766073^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226406937 10000000000 42224801766073 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669400541/1250000000 : ℝ), (-459380997/2000000000 : ℝ), (5226406937/10000000000 : ℝ)] ![(4361301078447/10000000000000 : ℝ), (14162187432911/100000000000000 : ℝ), (42224801766073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669400541/1250000000 : ℝ)|^4139 ≤ (4361301078447/10000000000000 : ℝ)^3115
        have hw : |(669400541/1250000000 : ℝ)|=(669400541/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-459380997/2000000000 : ℝ)|^4139 ≤ (14162187432911/100000000000000 : ℝ)^3115
        have hw : |(-459380997/2000000000 : ℝ)|=(459380997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5226406937/10000000000 : ℝ)|^4139 ≤ (42224801766073/100000000000000 : ℝ)^3115
        have hw : |(5226406937/10000000000 : ℝ)|=(5226406937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s3_2 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5355204243/10000000000 : ℝ)*x 0 + (5226407361/10000000000 : ℝ)*x 1 + (-2296904541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5355204243/10000000000 : ℝ)^4139 ≤ (5451626233083/12500000000000 : ℝ)^3115 := by
    have hnat : (5355204243 : ℕ)^4139*12500000000000^3115 ≤ 5451626233083^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5355204243 10000000000 5451626233083 12500000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5226407361/10000000000 : ℝ)^4139 ≤ (4222480631771/10000000000000 : ℝ)^3115 := by
    have hnat : (5226407361 : ℕ)^4139*10000000000000^3115 ≤ 4222480631771^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226407361 10000000000 4222480631771 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2296904541/10000000000 : ℝ)^4139 ≤ (3540545948843/25000000000000 : ℝ)^3115 := by
    have hnat : (2296904541 : ℕ)^4139*25000000000000^3115 ≤ 3540545948843^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296904541 10000000000 3540545948843 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5355204243/10000000000 : ℝ), (5226407361/10000000000 : ℝ), (-2296904541/10000000000 : ℝ)] ![(5451626233083/12500000000000 : ℝ), (4222480631771/10000000000000 : ℝ), (3540545948843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5355204243/10000000000 : ℝ)|^4139 ≤ (5451626233083/12500000000000 : ℝ)^3115
        have hw : |(5355204243/10000000000 : ℝ)|=(5355204243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5226407361/10000000000 : ℝ)|^4139 ≤ (4222480631771/10000000000000 : ℝ)^3115
        have hw : |(5226407361/10000000000 : ℝ)|=(5226407361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2296904541/10000000000 : ℝ)|^4139 ≤ (3540545948843/25000000000000 : ℝ)^3115
        have hw : |(-2296904541/10000000000 : ℝ)|=(2296904541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s3_3 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4370111209/10000000000 : ℝ)*x 0 + (4169457623/10000000000 : ℝ)*x 1 + (1145124287/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4370111209/10000000000 : ℝ)^4139 ≤ (16644888521939/50000000000000 : ℝ)^3115 := by
    have hnat : (4370111209 : ℕ)^4139*50000000000000^3115 ≤ 16644888521939^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370111209 10000000000 16644888521939 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4169457623/10000000000 : ℝ)^4139 ≤ (15637149408557/50000000000000 : ℝ)^3115 := by
    have hnat : (4169457623 : ℕ)^4139*50000000000000^3115 ≤ 15637149408557^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4169457623 10000000000 15637149408557 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145124287/2500000000 : ℝ)^4139 ≤ (1771796206207/5000000000000 : ℝ)^3115 := by
    have hnat : (1145124287 : ℕ)^4139*5000000000000^3115 ≤ 1771796206207^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145124287 2500000000 1771796206207 5000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4370111209/10000000000 : ℝ), (4169457623/10000000000 : ℝ), (1145124287/2500000000 : ℝ)] ![(16644888521939/50000000000000 : ℝ), (15637149408557/50000000000000 : ℝ), (1771796206207/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4370111209/10000000000 : ℝ)|^4139 ≤ (16644888521939/50000000000000 : ℝ)^3115
        have hw : |(4370111209/10000000000 : ℝ)|=(4370111209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4169457623/10000000000 : ℝ)|^4139 ≤ (15637149408557/50000000000000 : ℝ)^3115
        have hw : |(4169457623/10000000000 : ℝ)|=(4169457623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1145124287/2500000000 : ℝ)|^4139 ≤ (1771796206207/5000000000000 : ℝ)^3115
        have hw : |(1145124287/2500000000 : ℝ)|=(1145124287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s3_4 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2189981899/10000000000 : ℝ)*x 0 + (5227251689/10000000000 : ℝ)*x 1 + (1086899667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2189981899/10000000000 : ℝ)^4139 ≤ (132929771467/1000000000000 : ℝ)^3115 := by
    have hnat : (2189981899 : ℕ)^4139*1000000000000^3115 ≤ 132929771467^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189981899 10000000000 132929771467 1000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5227251689/10000000000 : ℝ)^4139 ≤ (42233870413947/100000000000000 : ℝ)^3115 := by
    have hnat : (5227251689 : ℕ)^4139*100000000000000^3115 ≤ 42233870413947^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227251689 10000000000 42233870413947 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086899667/2000000000 : ℝ)^4139 ≤ (8894630484571/20000000000000 : ℝ)^3115 := by
    have hnat : (1086899667 : ℕ)^4139*20000000000000^3115 ≤ 8894630484571^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086899667 2000000000 8894630484571 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2189981899/10000000000 : ℝ), (5227251689/10000000000 : ℝ), (1086899667/2000000000 : ℝ)] ![(132929771467/1000000000000 : ℝ), (42233870413947/100000000000000 : ℝ), (8894630484571/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2189981899/10000000000 : ℝ)|^4139 ≤ (132929771467/1000000000000 : ℝ)^3115
        have hw : |(-2189981899/10000000000 : ℝ)|=(2189981899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5227251689/10000000000 : ℝ)|^4139 ≤ (42233870413947/100000000000000 : ℝ)^3115
        have hw : |(5227251689/10000000000 : ℝ)|=(5227251689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086899667/2000000000 : ℝ)|^4139 ≤ (8894630484571/20000000000000 : ℝ)^3115
        have hw : |(1086899667/2000000000 : ℝ)|=(1086899667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s3_5 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302495263/10000000000 : ℝ)*x 0 + (-522203359/2500000000 : ℝ)*x 1 + (5434498633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302495263/10000000000 : ℝ)^4139 ≤ (43043557647503/100000000000000 : ℝ)^3115 := by
    have hnat : (5302495263 : ℕ)^4139*100000000000000^3115 ≤ 43043557647503^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302495263 10000000000 43043557647503 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522203359/2500000000 : ℝ)^4139 ≤ (12483286678171/100000000000000 : ℝ)^3115 := by
    have hnat : (522203359 : ℕ)^4139*100000000000000^3115 ≤ 12483286678171^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522203359 2500000000 12483286678171 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5434498633/10000000000 : ℝ)^4139 ≤ (44473155663207/100000000000000 : ℝ)^3115 := by
    have hnat : (5434498633 : ℕ)^4139*100000000000000^3115 ≤ 44473155663207^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434498633 10000000000 44473155663207 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302495263/10000000000 : ℝ), (-522203359/2500000000 : ℝ), (5434498633/10000000000 : ℝ)] ![(43043557647503/100000000000000 : ℝ), (12483286678171/100000000000000 : ℝ), (44473155663207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302495263/10000000000 : ℝ)|^4139 ≤ (43043557647503/100000000000000 : ℝ)^3115
        have hw : |(5302495263/10000000000 : ℝ)|=(5302495263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-522203359/2500000000 : ℝ)|^4139 ≤ (12483286678171/100000000000000 : ℝ)^3115
        have hw : |(-522203359/2500000000 : ℝ)|=(522203359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5434498633/10000000000 : ℝ)|^4139 ≤ (44473155663207/100000000000000 : ℝ)^3115
        have hw : |(5434498633/10000000000 : ℝ)|=(5434498633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s3_6 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302495429/10000000000 : ℝ)*x 0 + (1086899673/2000000000 : ℝ)*x 1 + (-1044406789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302495429/10000000000 : ℝ)^4139 ≤ (43043559437999/100000000000000 : ℝ)^3115 := by
    have hnat : (5302495429 : ℕ)^4139*100000000000000^3115 ≤ 43043559437999^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302495429 10000000000 43043559437999 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086899673/2000000000 : ℝ)^4139 ≤ (8894630549813/20000000000000 : ℝ)^3115 := by
    have hnat : (1086899673 : ℕ)^4139*20000000000000^3115 ≤ 8894630549813^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086899673 2000000000 8894630549813 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044406789/5000000000 : ℝ)^4139 ≤ (12483287805771/100000000000000 : ℝ)^3115 := by
    have hnat : (1044406789 : ℕ)^4139*100000000000000^3115 ≤ 12483287805771^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044406789 5000000000 12483287805771 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302495429/10000000000 : ℝ), (1086899673/2000000000 : ℝ), (-1044406789/5000000000 : ℝ)] ![(43043559437999/100000000000000 : ℝ), (8894630549813/20000000000000 : ℝ), (12483287805771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302495429/10000000000 : ℝ)|^4139 ≤ (43043559437999/100000000000000 : ℝ)^3115
        have hw : |(5302495429/10000000000 : ℝ)|=(5302495429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086899673/2000000000 : ℝ)|^4139 ≤ (8894630549813/20000000000000 : ℝ)^3115
        have hw : |(1086899673/2000000000 : ℝ)|=(1086899673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044406789/5000000000 : ℝ)|^4139 ≤ (12483287805771/100000000000000 : ℝ)^3115
        have hw : |(-1044406789/5000000000 : ℝ)|=(1044406789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s3_7 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1092538149/2500000000 : ℝ)*x 0 + (1144709087/2500000000 : ℝ)*x 1 + (4171128313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1092538149/2500000000 : ℝ)^4139 ≤ (16645097976779/50000000000000 : ℝ)^3115 := by
    have hnat : (1092538149 : ℕ)^4139*50000000000000^3115 ≤ 16645097976779^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092538149 2500000000 16645097976779 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1144709087/2500000000 : ℝ)^4139 ≤ (2213678317777/6250000000000 : ℝ)^3115 := by
    have hnat : (1144709087 : ℕ)^4139*6250000000000^3115 ≤ 2213678317777^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1144709087 2500000000 2213678317777 6250000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4171128313/10000000000 : ℝ)^4139 ≤ (312909509499/1000000000000 : ℝ)^3115 := by
    have hnat : (4171128313 : ℕ)^4139*1000000000000^3115 ≤ 312909509499^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171128313 10000000000 312909509499 1000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1092538149/2500000000 : ℝ), (1144709087/2500000000 : ℝ), (4171128313/10000000000 : ℝ)] ![(16645097976779/50000000000000 : ℝ), (2213678317777/6250000000000 : ℝ), (312909509499/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1092538149/2500000000 : ℝ)|^4139 ≤ (16645097976779/50000000000000 : ℝ)^3115
        have hw : |(1092538149/2500000000 : ℝ)|=(1092538149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1144709087/2500000000 : ℝ)|^4139 ≤ (2213678317777/6250000000000 : ℝ)^3115
        have hw : |(1144709087/2500000000 : ℝ)|=(1144709087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4171128313/10000000000 : ℝ)|^4139 ≤ (312909509499/1000000000000 : ℝ)^3115
        have hw : |(4171128313/10000000000 : ℝ)|=(4171128313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1085_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5229/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14879/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2201/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16679/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2201/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2201/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16679/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2201/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2201/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16679/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2201/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2201/25000 : ℝ) ^ (8277/2048 : ℝ) ≤ (1357876409216513/25000000000000000000 : ℝ) := by
    have hpowers : (2201/25000 : ℝ)^8277 ≤ (1357876409216513/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2201 : ℕ)^8277*25000000000000000000^2048 ≤ 1357876409216513^2048*25000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2201 25000 1357876409216513 25000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2201/25000 : ℝ)) (X := (1357876409216513/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16679/100000 : ℝ) ^ (8277/2048 : ℝ) ≤ (71845083140224799/100000000000000000000 : ℝ) := by
    have hpowers : (16679/100000 : ℝ)^8277 ≤ (71845083140224799/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16679 : ℕ)^8277*100000000000000000000^2048 ≤ 71845083140224799^2048*100000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16679 100000 71845083140224799 100000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16679/100000 : ℝ)) (X := (71845083140224799/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501357876409216513/12500000000000000000 : ℝ) ≤ (10000268775374719/10000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (12501357876409216513/12500000000000000000 : ℝ)^2048 ≤ (10000268775374719/10000000000000000 : ℝ)^8277 := by
      have hnat : (12501357876409216513 : ℕ)^2048*10000000000000000^8277 ≤ 10000268775374719^8277*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501357876409216513 12500000000000000000 10000268775374719 10000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000268775374719/10000000000000000 : ℝ)) (X := (12501357876409216513/12500000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100077276588777090851/100000000000000000000 : ℝ) ≤ (1250238939916563/1250000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (100077276588777090851/100000000000000000000 : ℝ)^2048 ≤ (1250238939916563/1250000000000000 : ℝ)^8277 := by
      have hnat : (100077276588777090851 : ℕ)^2048*1250000000000000^8277 ≤ 1250238939916563^8277*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100077276588777090851 100000000000000000000 1250238939916563 1250000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250238939916563/1250000000000000 : ℝ)) (X := (100077276588777090851/100000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50071845083140224799/50000000000000000000 : ℝ) ≤ (10003554263290289/10000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (50071845083140224799/50000000000000000000 : ℝ)^2048 ≤ (10003554263290289/10000000000000000 : ℝ)^8277 := by
      have hnat : (50071845083140224799 : ℕ)^2048*10000000000000000^8277 ≤ 10003554263290289^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50071845083140224799 50000000000000000000 10003554263290289 10000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003554263290289/10000000000000000 : ℝ)) (X := (50071845083140224799/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1357876409216513/25000000000000000000 : ℝ) ≤ ((2249234033441920967/2250000000000000000 : ℝ)+2*(46935541651/22500000000000 : ℝ)*(2201/25000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (2249234033441920967/2250000000000000000 : ℝ)+2*(46935541651/22500000000000 : ℝ)*(2201/25000 : ℝ)=(10000268775374719/10000000000000000 : ℝ) by norm_num, show 1+2*(1357876409216513/25000000000000000000 : ℝ)=(12501357876409216513/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(71845083140224799/100000000000000000000 : ℝ)+(1357876409216513/25000000000000000000 : ℝ) ≤ ((2249234033441920967/2250000000000000000 : ℝ)+(46935541651/22500000000000 : ℝ)*((16679/100000 : ℝ)+(2201/25000 : ℝ)))^(8277/2048 : ℝ) := by
    rw [show (2249234033441920967/2250000000000000000 : ℝ)+(46935541651/22500000000000 : ℝ)*((16679/100000 : ℝ)+(2201/25000 : ℝ))=(1250238939916563/1250000000000000 : ℝ) by norm_num, show 1+(71845083140224799/100000000000000000000 : ℝ)+(1357876409216513/25000000000000000000 : ℝ)=(100077276588777090851/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(71845083140224799/100000000000000000000 : ℝ) ≤ ((2249234033441920967/2250000000000000000 : ℝ)+2*(46935541651/22500000000000 : ℝ)*(16679/100000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (2249234033441920967/2250000000000000000 : ℝ)+2*(46935541651/22500000000000 : ℝ)*(16679/100000 : ℝ)=(10003554263290289/10000000000000000 : ℝ) by norm_num, show 1+2*(71845083140224799/100000000000000000000 : ℝ)=(50071845083140224799/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2249234033441920967/2250000000000000000 : ℝ)*(X 1 0+X 2 0)+(46935541651/22500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (2201/25000 : ℝ)) (hi := (16679/100000 : ℝ)) (c := (2249234033441920967/2250000000000000000 : ℝ)) (alpha := (46935541651/22500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2249234033441920967/2250000000000000000 : ℝ)*(X 0 1+X 2 1)+(46935541651/22500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (2201/25000 : ℝ)) (hi := (16679/100000 : ℝ)) (c := (2249234033441920967/2250000000000000000 : ℝ)) (alpha := (46935541651/22500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2249234033441920967/2250000000000000000 : ℝ)*(X 0 2+X 1 2)+(46935541651/22500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (2201/25000 : ℝ)) (hi := (16679/100000 : ℝ)) (c := (2249234033441920967/2250000000000000000 : ℝ)) (alpha := (46935541651/22500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2189960619/10000000000 : ℝ)*X 0 0+(5435348061/10000000000 : ℝ)*X 0 1+(209056279/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669400541/1250000000 : ℝ)*X 1 0+(-459380997/2000000000 : ℝ)*X 1 1+(5226406937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5355204243/10000000000 : ℝ)*X 2 0+(5226407361/10000000000 : ℝ)*X 2 1+(-2296904541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4370111209/10000000000 : ℝ)*X 0 0+(4169457623/10000000000 : ℝ)*X 0 1+(1145124287/2500000000 : ℝ)*X 0 2+(4370111209/10000000000 : ℝ)*X 1 0+(4169457623/10000000000 : ℝ)*X 1 1+(1145124287/2500000000 : ℝ)*X 1 2+(4370111209/10000000000 : ℝ)*X 2 0+(4169457623/10000000000 : ℝ)*X 2 1+(1145124287/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2189981899/10000000000 : ℝ)*X 0 0+(5227251689/10000000000 : ℝ)*X 0 1+(1086899667/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302495263/10000000000 : ℝ)*X 1 0+(-522203359/2500000000 : ℝ)*X 1 1+(5434498633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302495429/10000000000 : ℝ)*X 2 0+(1086899673/2000000000 : ℝ)*X 2 1+(-1044406789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1092538149/2500000000 : ℝ)*X 0 0+(1144709087/2500000000 : ℝ)*X 0 1+(4171128313/10000000000 : ℝ)*X 0 2+(1092538149/2500000000 : ℝ)*X 1 0+(1144709087/2500000000 : ℝ)*X 1 1+(4171128313/10000000000 : ℝ)*X 1 2+(1092538149/2500000000 : ℝ)*X 2 0+(1144709087/2500000000 : ℝ)*X 2 1+(4171128313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (282267980699939056797979033/37500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1980462329/100000000000000 : ℝ)*(base19) + (747286429/50000000000000 : ℝ)*(base23) + (13720113/6250000000000 : ℝ)*(lower2) + (95862587/100000000000000 : ℝ)*(upper3) + (51333583/25000000000000 : ℝ)*(upper5) + (902374795081731/25000000000000 : ℝ)*(major0) + (902374795081731/25000000000000 : ℝ)*(major1) + (144379967213077/4000000000000 : ℝ)*(major2) + (4786071107290523/100000000000000 : ℝ)*(sp0) + (149565908676911/3125000000000 : ℝ)*(sp1) + (2393054781775311/50000000000000 : ℝ)*(sp2) + (1216435799162517/50000000000000 : ℝ)*(sp3) + (39950832957/100000000000000 : ℝ)*(sp4) + (15453300453/100000000000000 : ℝ)*(sp7) + (152055440726593/6250000000000 : ℝ)*(f.failure) + (119652776453087/2500000000000 : ℝ)*(f.sum) + (15228331316801/2250000000000000000000000000 : ℝ)*base66 + (57034918999428877/56250000000000000000000000000000 : ℝ)*base67 + (23159487059981459/9000000000000000000000000000000 : ℝ)*base69 + (514772084950571123/56250000000000000000000000000000 : ℝ)*base72 + (1771354476199/2250000000000000000000000000 : ℝ)*base73 + (139169604923981459/9000000000000000000000000000000 : ℝ)*base75 + (55901170394927347/6250000000000000000000000000000 : ℝ)*base78 + (53356214944927347/6250000000000000000000000000000 : ℝ)*base80 + (173170799117/375000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11854249/625000000000000000000 : ℝ)*base89 + (11854249/625000000000000000000 : ℝ)*base91 + (5604249/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (118360167251488677533250317/18750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (577947491/50000000000000 : ℝ)*(base19) + (61288601/4000000000000 : ℝ)*(base23) + (6722121/3125000000000 : ℝ)*(upper3) + (95219331/100000000000000 : ℝ)*(lower4) + (38573127/100000000000000 : ℝ)*(upper5) + (1819475154293051/50000000000000 : ℝ)*(major0) + (1819475154293051/50000000000000 : ℝ)*(major1) + (1819475154293051/50000000000000 : ℝ)*(major2) + (21932926481/100000000000000 : ℝ)*(sp1) + (1326466237/5000000000000 : ℝ)*(sp2) + (4825162604368517/100000000000000 : ℝ)*(sp4) + (4825139515547053/100000000000000 : ℝ)*(sp5) + (4825134542828753/100000000000000 : ℝ)*(sp6) + (613184450596401/25000000000000 : ℝ)*(sp7) + (613184450596401/25000000000000 : ℝ)*(f.failure) + (4825162604368517/100000000000000 : ℝ)*(f.sum) + (315417258277/1125000000000000000000000000 : ℝ)*base65 + (343641393014366561/37500000000000000000000000000000 : ℝ)*base68 + (245204487089366561/37500000000000000000000000000000 : ℝ)*base70 + (99168421260633439/37500000000000000000000000000000 : ℝ)*base71 + (8577671851973/1125000000000000000000000000 : ℝ)*base74 + (451464585998133439/37500000000000000000000000000000 : ℝ)*base75 + (236157409364366561/37500000000000000000000000000000 : ℝ)*base78 + (151724821964366561/37500000000000000000000000000000 : ℝ)*base80 + (839426732087/281250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (18107993/2500000000000000000000 : ℝ)*base89 + (18107993/2500000000000000000000 : ℝ)*base91 + (18107993/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1085_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14879/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1085_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1085_s4_0 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219345807/1000000000 : ℝ)*x 0 + (2702390519/5000000000 : ℝ)*x 1 + (5254688317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219345807/1000000000 : ℝ)^4139 ≤ (1332102072917/10000000000000 : ℝ)^3115 := by
    have hnat : (219345807 : ℕ)^4139*10000000000000^3115 ≤ 1332102072917^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219345807 1000000000 1332102072917 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702390519/5000000000 : ℝ)^4139 ≤ (22075153684321/50000000000000 : ℝ)^3115 := by
    have hnat : (2702390519 : ℕ)^4139*50000000000000^3115 ≤ 22075153684321^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702390519 5000000000 22075153684321 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254688317/10000000000 : ℝ)^4139 ≤ (2658041993203/6250000000000 : ℝ)^3115 := by
    have hnat : (5254688317 : ℕ)^4139*6250000000000^3115 ≤ 2658041993203^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254688317 10000000000 2658041993203 6250000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219345807/1000000000 : ℝ), (2702390519/5000000000 : ℝ), (5254688317/10000000000 : ℝ)] ![(1332102072917/10000000000000 : ℝ), (22075153684321/50000000000000 : ℝ), (2658041993203/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219345807/1000000000 : ℝ)|^4139 ≤ (1332102072917/10000000000000 : ℝ)^3115
        have hw : |(-219345807/1000000000 : ℝ)|=(219345807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702390519/5000000000 : ℝ)|^4139 ≤ (22075153684321/50000000000000 : ℝ)^3115
        have hw : |(2702390519/5000000000 : ℝ)|=(2702390519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254688317/10000000000 : ℝ)|^4139 ≤ (2658041993203/6250000000000 : ℝ)^3115
        have hw : |(5254688317/10000000000 : ℝ)|=(5254688317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s4_1 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673808209/5000000000 : ℝ)*x 0 + (-2269781253/10000000000 : ℝ)*x 1 + (5254688721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673808209/5000000000 : ℝ)^4139 ≤ (2720682453039/6250000000000 : ℝ)^3115 := by
    have hnat : (2673808209 : ℕ)^4139*6250000000000^3115 ≤ 2720682453039^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673808209 5000000000 2720682453039 6250000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2269781253/10000000000 : ℝ)^4139 ≤ (13940404504229/100000000000000 : ℝ)^3115 := by
    have hnat : (2269781253 : ℕ)^4139*100000000000000^3115 ≤ 13940404504229^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2269781253 10000000000 13940404504229 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5254688721/10000000000 : ℝ)^4139 ≤ (21264338117943/50000000000000 : ℝ)^3115 := by
    have hnat : (5254688721 : ℕ)^4139*50000000000000^3115 ≤ 21264338117943^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254688721 10000000000 21264338117943 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673808209/5000000000 : ℝ), (-2269781253/10000000000 : ℝ), (5254688721/10000000000 : ℝ)] ![(2720682453039/6250000000000 : ℝ), (13940404504229/100000000000000 : ℝ), (21264338117943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673808209/5000000000 : ℝ)|^4139 ≤ (2720682453039/6250000000000 : ℝ)^3115
        have hw : |(2673808209/5000000000 : ℝ)|=(2673808209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2269781253/10000000000 : ℝ)|^4139 ≤ (13940404504229/100000000000000 : ℝ)^3115
        have hw : |(-2269781253/10000000000 : ℝ)|=(2269781253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5254688721/10000000000 : ℝ)|^4139 ≤ (21264338117943/50000000000000 : ℝ)^3115
        have hw : |(5254688721/10000000000 : ℝ)|=(5254688721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s4_2 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347616721/10000000000 : ℝ)*x 0 + (5254688459/10000000000 : ℝ)*x 1 + (-567445299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347616721/10000000000 : ℝ)^4139 ≤ (21765461262967/50000000000000 : ℝ)^3115 := by
    have hnat : (5347616721 : ℕ)^4139*50000000000000^3115 ≤ 21765461262967^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347616721 10000000000 21765461262967 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254688459/10000000000 : ℝ)^4139 ≤ (10632168354581/25000000000000 : ℝ)^3115 := by
    have hnat : (5254688459 : ℕ)^4139*25000000000000^3115 ≤ 10632168354581^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254688459 10000000000 10632168354581 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567445299/2500000000 : ℝ)^4139 ≤ (3485101009767/25000000000000 : ℝ)^3115 := by
    have hnat : (567445299 : ℕ)^4139*25000000000000^3115 ≤ 3485101009767^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567445299 2500000000 3485101009767 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347616721/10000000000 : ℝ), (5254688459/10000000000 : ℝ), (-567445299/2500000000 : ℝ)] ![(21765461262967/50000000000000 : ℝ), (10632168354581/25000000000000 : ℝ), (3485101009767/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347616721/10000000000 : ℝ)|^4139 ≤ (21765461262967/50000000000000 : ℝ)^3115
        have hw : |(5347616721/10000000000 : ℝ)|=(5347616721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254688459/10000000000 : ℝ)|^4139 ≤ (10632168354581/25000000000000 : ℝ)^3115
        have hw : |(5254688459/10000000000 : ℝ)|=(5254688459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-567445299/2500000000 : ℝ)|^4139 ≤ (3485101009767/25000000000000 : ℝ)^3115
        have hw : |(-567445299/2500000000 : ℝ)|=(567445299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s4_3 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2186096311/5000000000 : ℝ)*x 0 + (845414001/2000000000 : ℝ)*x 1 + (4522340369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2186096311/5000000000 : ℝ)^4139 ≤ (33310846243091/100000000000000 : ℝ)^3115 := by
    have hnat : (2186096311 : ℕ)^4139*100000000000000^3115 ≤ 33310846243091^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186096311 5000000000 33310846243091 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845414001/2000000000 : ℝ)^4139 ≤ (31849796307201/100000000000000 : ℝ)^3115 := by
    have hnat : (845414001 : ℕ)^4139*100000000000000^3115 ≤ 31849796307201^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845414001 2000000000 31849796307201 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4522340369/10000000000 : ℝ)^4139 ≤ (272182479951/781250000000 : ℝ)^3115 := by
    have hnat : (4522340369 : ℕ)^4139*781250000000^3115 ≤ 272182479951^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522340369 10000000000 272182479951 781250000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2186096311/5000000000 : ℝ), (845414001/2000000000 : ℝ), (4522340369/10000000000 : ℝ)] ![(33310846243091/100000000000000 : ℝ), (31849796307201/100000000000000 : ℝ), (272182479951/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2186096311/5000000000 : ℝ)|^4139 ≤ (33310846243091/100000000000000 : ℝ)^3115
        have hw : |(2186096311/5000000000 : ℝ)|=(2186096311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845414001/2000000000 : ℝ)|^4139 ≤ (31849796307201/100000000000000 : ℝ)^3115
        have hw : |(845414001/2000000000 : ℝ)|=(845414001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4522340369/10000000000 : ℝ)|^4139 ≤ (272182479951/781250000000 : ℝ)^3115
        have hw : |(4522340369/10000000000 : ℝ)|=(4522340369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s4_4 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096732609/5000000000 : ℝ)*x 0 + (5255125351/10000000000 : ℝ)*x 1 + (1080868541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096732609/5000000000 : ℝ)^4139 ≤ (13321078409843/100000000000000 : ℝ)^3115 := by
    have hnat : (1096732609 : ℕ)^4139*100000000000000^3115 ≤ 13321078409843^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096732609 5000000000 13321078409843 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255125351/10000000000 : ℝ)^4139 ≤ (10633342960743/25000000000000 : ℝ)^3115 := by
    have hnat : (5255125351 : ℕ)^4139*25000000000000^3115 ≤ 10633342960743^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255125351 10000000000 10633342960743 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1080868541/2000000000 : ℝ)^4139 ≤ (44145549730787/100000000000000 : ℝ)^3115 := by
    have hnat : (1080868541 : ℕ)^4139*100000000000000^3115 ≤ 44145549730787^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080868541 2000000000 44145549730787 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096732609/5000000000 : ℝ), (5255125351/10000000000 : ℝ), (1080868541/2000000000 : ℝ)] ![(13321078409843/100000000000000 : ℝ), (10633342960743/25000000000000 : ℝ), (44145549730787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096732609/5000000000 : ℝ)|^4139 ≤ (13321078409843/100000000000000 : ℝ)^3115
        have hw : |(-1096732609/5000000000 : ℝ)|=(1096732609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255125351/10000000000 : ℝ)|^4139 ≤ (10633342960743/25000000000000 : ℝ)^3115
        have hw : |(5255125351/10000000000 : ℝ)|=(5255125351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1080868541/2000000000 : ℝ)|^4139 ≤ (44145549730787/100000000000000 : ℝ)^3115
        have hw : |(1080868541/2000000000 : ℝ)|=(1080868541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s4_5 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5309756757/10000000000 : ℝ)*x 0 + (-1060063383/5000000000 : ℝ)*x 1 + (5404342709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309756757/10000000000 : ℝ)^4139 ≤ (43121898617279/100000000000000 : ℝ)^3115 := by
    have hnat : (5309756757 : ℕ)^4139*100000000000000^3115 ≤ 43121898617279^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309756757 10000000000 43121898617279 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060063383/5000000000 : ℝ)^4139 ≤ (3183137897851/25000000000000 : ℝ)^3115 := by
    have hnat : (1060063383 : ℕ)^4139*25000000000000^3115 ≤ 3183137897851^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060063383 5000000000 3183137897851 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404342709/10000000000 : ℝ)^4139 ≤ (22072774887101/50000000000000 : ℝ)^3115 := by
    have hnat : (5404342709 : ℕ)^4139*50000000000000^3115 ≤ 22072774887101^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404342709 10000000000 22072774887101 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309756757/10000000000 : ℝ), (-1060063383/5000000000 : ℝ), (5404342709/10000000000 : ℝ)] ![(43121898617279/100000000000000 : ℝ), (3183137897851/25000000000000 : ℝ), (22072774887101/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309756757/10000000000 : ℝ)|^4139 ≤ (43121898617279/100000000000000 : ℝ)^3115
        have hw : |(5309756757/10000000000 : ℝ)|=(5309756757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1060063383/5000000000 : ℝ)|^4139 ≤ (3183137897851/25000000000000 : ℝ)^3115
        have hw : |(-1060063383/5000000000 : ℝ)|=(1060063383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404342709/10000000000 : ℝ)|^4139 ≤ (22072774887101/50000000000000 : ℝ)^3115
        have hw : |(5404342709/10000000000 : ℝ)|=(5404342709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s4_6 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331859789/625000000 : ℝ)*x 0 + (1351085661/2500000000 : ℝ)*x 1 + (-424025407/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331859789/625000000 : ℝ)^4139 ≤ (43121897182079/100000000000000 : ℝ)^3115 := by
    have hnat : (331859789 : ℕ)^4139*100000000000000^3115 ≤ 43121897182079^3115*625000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331859789 625000000 43121897182079 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351085661/2500000000 : ℝ)^4139 ≤ (8829109813741/20000000000000 : ℝ)^3115 := by
    have hnat : (1351085661 : ℕ)^4139*20000000000000^3115 ≤ 8829109813741^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351085661 2500000000 8829109813741 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424025407/2000000000 : ℝ)^4139 ≤ (2546510747593/20000000000000 : ℝ)^3115 := by
    have hnat : (424025407 : ℕ)^4139*20000000000000^3115 ≤ 2546510747593^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424025407 2000000000 2546510747593 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331859789/625000000 : ℝ), (1351085661/2500000000 : ℝ), (-424025407/2000000000 : ℝ)] ![(43121897182079/100000000000000 : ℝ), (8829109813741/20000000000000 : ℝ), (2546510747593/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331859789/625000000 : ℝ)|^4139 ≤ (43121897182079/100000000000000 : ℝ)^3115
        have hw : |(331859789/625000000 : ℝ)|=(331859789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351085661/2500000000 : ℝ)|^4139 ≤ (8829109813741/20000000000000 : ℝ)^3115
        have hw : |(1351085661/2500000000 : ℝ)|=(1351085661/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424025407/2000000000 : ℝ)|^4139 ≤ (2546510747593/20000000000000 : ℝ)^3115
        have hw : |(-424025407/2000000000 : ℝ)|=(424025407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s4_7 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (874441583/2000000000 : ℝ)*x 0 + (4521481403/10000000000 : ℝ)*x 1 + (422793273/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874441583/2000000000 : ℝ)^4139 ≤ (16655500529697/50000000000000 : ℝ)^3115 := by
    have hnat : (874441583 : ℕ)^4139*50000000000000^3115 ≤ 16655500529697^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874441583 2000000000 16655500529697 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4521481403/10000000000 : ℝ)^4139 ≤ (34830565049057/100000000000000 : ℝ)^3115 := by
    have hnat : (4521481403 : ℕ)^4139*100000000000000^3115 ≤ 34830565049057^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4521481403 10000000000 34830565049057 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422793273/1000000000 : ℝ)^4139 ≤ (7964608469129/25000000000000 : ℝ)^3115 := by
    have hnat : (422793273 : ℕ)^4139*25000000000000^3115 ≤ 7964608469129^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422793273 1000000000 7964608469129 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874441583/2000000000 : ℝ), (4521481403/10000000000 : ℝ), (422793273/1000000000 : ℝ)] ![(16655500529697/50000000000000 : ℝ), (34830565049057/100000000000000 : ℝ), (7964608469129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874441583/2000000000 : ℝ)|^4139 ≤ (16655500529697/50000000000000 : ℝ)^3115
        have hw : |(874441583/2000000000 : ℝ)|=(874441583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4521481403/10000000000 : ℝ)|^4139 ≤ (34830565049057/100000000000000 : ℝ)^3115
        have hw : |(4521481403/10000000000 : ℝ)|=(4521481403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(422793273/1000000000 : ℝ)|^4139 ≤ (7964608469129/25000000000000 : ℝ)^3115
        have hw : |(422793273/1000000000 : ℝ)|=(422793273/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1085_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5531/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (89/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5229/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14879/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5229/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5229/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14879/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5229/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5229/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14879/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5229/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5229/50000 : ℝ) ^ (8277/2048 : ℝ) ≤ (10891754358686521/100000000000000000000 : ℝ) := by
    have hpowers : (5229/50000 : ℝ)^8277 ≤ (10891754358686521/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5229 : ℕ)^8277*100000000000000000000^2048 ≤ 10891754358686521^2048*50000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5229 50000 10891754358686521 100000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5229/50000 : ℝ)) (X := (10891754358686521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14879/100000 : ℝ) ^ (8277/2048 : ℝ) ≤ (22642457313032539/50000000000000000000 : ℝ) := by
    have hpowers : (14879/100000 : ℝ)^8277 ≤ (22642457313032539/50000000000000000000 : ℝ)^2048 := by
      have hnat : (14879 : ℕ)^8277*50000000000000000000^2048 ≤ 22642457313032539^2048*100000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14879 100000 22642457313032539 50000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14879/100000 : ℝ)) (X := (22642457313032539/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010891754358686521/50000000000000000000 : ℝ) ≤ (2000107790188523/2000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (50010891754358686521/50000000000000000000 : ℝ)^2048 ≤ (2000107790188523/2000000000000000 : ℝ)^8277 := by
      have hnat : (50010891754358686521 : ℕ)^2048*2000000000000000^8277 ≤ 2000107790188523^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010891754358686521 50000000000000000000 2000107790188523 2000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000107790188523/2000000000000000 : ℝ)) (X := (50010891754358686521/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100056176668984751599/100000000000000000000 : ℝ) ≤ (1250173712556497/1250000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (100056176668984751599/100000000000000000000 : ℝ)^2048 ≤ (1250173712556497/1250000000000000 : ℝ)^8277 := by
      have hnat : (100056176668984751599 : ℕ)^2048*1250000000000000^8277 ≤ 1250173712556497^8277*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100056176668984751599 100000000000000000000 1250173712556497 1250000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250173712556497/1250000000000000 : ℝ)) (X := (100056176668984751599/100000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25022642457313032539/25000000000000000000 : ℝ) ≤ (10002240449961337/10000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (25022642457313032539/25000000000000000000 : ℝ)^2048 ≤ (10002240449961337/10000000000000000 : ℝ)^8277 := by
      have hnat : (25022642457313032539 : ℕ)^2048*10000000000000000^8277 ≤ 10002240449961337^8277*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25022642457313032539 25000000000000000000 10002240449961337 10000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002240449961337/10000000000000000 : ℝ)) (X := (25022642457313032539/25000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10891754358686521/100000000000000000000 : ℝ) ≤ ((44194588425379506239/44210000000000000000 : ℝ)+2*(850749509361/442100000000000 : ℝ)*(5229/50000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (44194588425379506239/44210000000000000000 : ℝ)+2*(850749509361/442100000000000 : ℝ)*(5229/50000 : ℝ)=(2000107790188523/2000000000000000 : ℝ) by norm_num, show 1+2*(10891754358686521/100000000000000000000 : ℝ)=(50010891754358686521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22642457313032539/50000000000000000000 : ℝ)+(10891754358686521/100000000000000000000 : ℝ) ≤ ((44194588425379506239/44210000000000000000 : ℝ)+(850749509361/442100000000000 : ℝ)*((14879/100000 : ℝ)+(5229/50000 : ℝ)))^(8277/2048 : ℝ) := by
    rw [show (44194588425379506239/44210000000000000000 : ℝ)+(850749509361/442100000000000 : ℝ)*((14879/100000 : ℝ)+(5229/50000 : ℝ))=(1250173712556497/1250000000000000 : ℝ) by norm_num, show 1+(22642457313032539/50000000000000000000 : ℝ)+(10891754358686521/100000000000000000000 : ℝ)=(100056176668984751599/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22642457313032539/50000000000000000000 : ℝ) ≤ ((44194588425379506239/44210000000000000000 : ℝ)+2*(850749509361/442100000000000 : ℝ)*(14879/100000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (44194588425379506239/44210000000000000000 : ℝ)+2*(850749509361/442100000000000 : ℝ)*(14879/100000 : ℝ)=(10002240449961337/10000000000000000 : ℝ) by norm_num, show 1+2*(22642457313032539/50000000000000000000 : ℝ)=(25022642457313032539/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44194588425379506239/44210000000000000000 : ℝ)*(X 1 0+X 2 0)+(850749509361/442100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (5229/50000 : ℝ)) (hi := (14879/100000 : ℝ)) (c := (44194588425379506239/44210000000000000000 : ℝ)) (alpha := (850749509361/442100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44194588425379506239/44210000000000000000 : ℝ)*(X 0 1+X 2 1)+(850749509361/442100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (5229/50000 : ℝ)) (hi := (14879/100000 : ℝ)) (c := (44194588425379506239/44210000000000000000 : ℝ)) (alpha := (850749509361/442100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44194588425379506239/44210000000000000000 : ℝ)*(X 0 2+X 1 2)+(850749509361/442100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (5229/50000 : ℝ)) (hi := (14879/100000 : ℝ)) (c := (44194588425379506239/44210000000000000000 : ℝ)) (alpha := (850749509361/442100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-219345807/1000000000 : ℝ)*X 0 0+(2702390519/5000000000 : ℝ)*X 0 1+(5254688317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673808209/5000000000 : ℝ)*X 1 0+(-2269781253/10000000000 : ℝ)*X 1 1+(5254688721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347616721/10000000000 : ℝ)*X 2 0+(5254688459/10000000000 : ℝ)*X 2 1+(-567445299/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2186096311/5000000000 : ℝ)*X 0 0+(845414001/2000000000 : ℝ)*X 0 1+(4522340369/10000000000 : ℝ)*X 0 2+(2186096311/5000000000 : ℝ)*X 1 0+(845414001/2000000000 : ℝ)*X 1 1+(4522340369/10000000000 : ℝ)*X 1 2+(2186096311/5000000000 : ℝ)*X 2 0+(845414001/2000000000 : ℝ)*X 2 1+(4522340369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1096732609/5000000000 : ℝ)*X 0 0+(5255125351/10000000000 : ℝ)*X 0 1+(1080868541/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309756757/10000000000 : ℝ)*X 1 0+(-1060063383/5000000000 : ℝ)*X 1 1+(5404342709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331859789/625000000 : ℝ)*X 2 0+(1351085661/2500000000 : ℝ)*X 2 1+(-424025407/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((874441583/2000000000 : ℝ)*X 0 0+(4521481403/10000000000 : ℝ)*X 0 1+(422793273/1000000000 : ℝ)*X 0 2+(874441583/2000000000 : ℝ)*X 1 0+(4521481403/10000000000 : ℝ)*X 1 1+(422793273/1000000000 : ℝ)*X 1 2+(874441583/2000000000 : ℝ)*X 2 0+(4521481403/10000000000 : ℝ)*X 2 1+(422793273/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5029216405752698559783257301/1105250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (370384331/20000000000000 : ℝ)*(base19) + (946189843/50000000000000 : ℝ)*(base23) + (20483793/6250000000000 : ℝ)*(upper3) + (352037/195312500000 : ℝ)*(upper4) + (116065263/50000000000000 : ℝ)*(upper5) + (2512357285696349/50000000000000 : ℝ)*(major0) + (2512357285696349/50000000000000 : ℝ)*(major1) + (2512357285696349/50000000000000 : ℝ)*(major2) + (6662598786318227/100000000000000 : ℝ)*(sp0) + (3331325871172209/50000000000000 : ℝ)*(sp1) + (1665662925471597/25000000000000 : ℝ)*(sp2) + (1693374254634179/50000000000000 : ℝ)*(sp3) + (27403973923/50000000000000 : ℝ)*(sp4) + (6721893591/25000000000000 : ℝ)*(sp7) + (3386775396842723/100000000000000 : ℝ)*(f.failure) + (3331326797133037/50000000000000 : ℝ)*(f.sum) + (964706755693/1381562500000000000000000000 : ℝ)*base65 + (27918963808836921411/2210500000000000000000000000000000 : ℝ)*base67 + (6147048233288421411/2210500000000000000000000000000000 : ℝ)*base69 + (28021923580373921411/2210500000000000000000000000000000 : ℝ)*base71 + (1346228318231/11052500000000000000000000000 : ℝ)*base74 + (12888427791603921411/2210500000000000000000000000000000 : ℝ)*base75 + (27571779517821921411/2210500000000000000000000000000000 : ℝ)*base77 + (66317620053376921411/2210500000000000000000000000000000 : ℝ)*base79 + (22900989412927/5526250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (33994661/10000000000000000000000 : ℝ)*base90 + (33994661/10000000000000000000000 : ℝ)*base92 + (33994661/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4374356492435290907487710331/1105250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183335329/20000000000000 : ℝ)*(base19) + (1168906853/100000000000000 : ℝ)*(base23) + (563069/12500000000000 : ℝ)*(lower3) + (9341781/4000000000000 : ℝ)*(lower4) + (2527053830241543/50000000000000 : ℝ)*(major0) + (2527053830241543/50000000000000 : ℝ)*(major1) + (2527053830241543/50000000000000 : ℝ)*(major2) + (210288909/20000000000000 : ℝ)*(sp0) + (14840690477/50000000000000 : ℝ)*(sp1) + (6727922593/25000000000000 : ℝ)*(sp2) + (3350813554876167/50000000000000 : ℝ)*(sp4) + (6701597563139281/100000000000000 : ℝ)*(sp5) + (3350800040299827/50000000000000 : ℝ)*(sp6) + (85164675696067/2500000000000 : ℝ)*(sp7) + (85164675696067/2500000000000 : ℝ)*(f.failure) + (6701628161196879/100000000000000 : ℝ)*(f.sum) + (2223046427243/2763125000000000000000000000 : ℝ)*base66 + (11988350807284213223/2210500000000000000000000000000000 : ℝ)*base68 + (12035841432180286777/2210500000000000000000000000000000 : ℝ)*base69 + (12971912130186713223/2210500000000000000000000000000000 : ℝ)*base72 + (8843051536843/11052500000000000000000000000 : ℝ)*base73 + (1044500151613713223/2210500000000000000000000000000000 : ℝ)*base76 + (8125666157913786777/2210500000000000000000000000000000 : ℝ)*base77 + (7731601965574213223/2210500000000000000000000000000000 : ℝ)*base80 + (545163853883/690781250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4235131/250000000000000000000 : ℝ)*base89 + (4235131/250000000000000000000 : ℝ)*base91 + (4235131/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1085_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14879/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5229/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5531/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (89/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1085_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1085_s5_0 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-438846947/2000000000 : ℝ)*x 0 + (5396457629/10000000000 : ℝ)*x 1 + (5262502289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (438846947/2000000000 : ℝ)^4139 ≤ (3331822094119/25000000000000 : ℝ)^3115 := by
    have hnat : (438846947 : ℕ)^4139*25000000000000^3115 ≤ 3331822094119^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438846947 2000000000 3331822094119 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396457629/10000000000 : ℝ)^4139 ≤ (1762399492027/4000000000000 : ℝ)^3115 := by
    have hnat : (5396457629 : ℕ)^4139*4000000000000^3115 ≤ 1762399492027^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396457629 10000000000 1762399492027 4000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262502289/10000000000 : ℝ)^4139 ≤ (4261272430463/10000000000000 : ℝ)^3115 := by
    have hnat : (5262502289 : ℕ)^4139*10000000000000^3115 ≤ 4261272430463^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262502289 10000000000 4261272430463 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-438846947/2000000000 : ℝ), (5396457629/10000000000 : ℝ), (5262502289/10000000000 : ℝ)] ![(3331822094119/25000000000000 : ℝ), (1762399492027/4000000000000 : ℝ), (4261272430463/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-438846947/2000000000 : ℝ)|^4139 ≤ (3331822094119/25000000000000 : ℝ)^3115
        have hw : |(-438846947/2000000000 : ℝ)|=(438846947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396457629/10000000000 : ℝ)|^4139 ≤ (1762399492027/4000000000000 : ℝ)^3115
        have hw : |(5396457629/10000000000 : ℝ)|=(5396457629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262502289/10000000000 : ℝ)|^4139 ≤ (4261272430463/10000000000000 : ℝ)^3115
        have hw : |(5262502289/10000000000 : ℝ)|=(5262502289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s5_1 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66819247/125000000 : ℝ)*x 0 + (-2262229101/10000000000 : ℝ)*x 1 + (131562579/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66819247/125000000 : ℝ)^4139 ≤ (4350845912091/10000000000000 : ℝ)^3115 := by
    have hnat : (66819247 : ℕ)^4139*10000000000000^3115 ≤ 4350845912091^3115*125000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66819247 125000000 4350845912091 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262229101/10000000000 : ℝ)^4139 ≤ (6939403599283/50000000000000 : ℝ)^3115 := by
    have hnat : (2262229101 : ℕ)^4139*50000000000000^3115 ≤ 6939403599283^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262229101 10000000000 6939403599283 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131562579/250000000 : ℝ)^4139 ≤ (10653183418997/25000000000000 : ℝ)^3115 := by
    have hnat : (131562579 : ℕ)^4139*25000000000000^3115 ≤ 10653183418997^3115*250000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131562579 250000000 10653183418997 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66819247/125000000 : ℝ), (-2262229101/10000000000 : ℝ), (131562579/250000000 : ℝ)] ![(4350845912091/10000000000000 : ℝ), (6939403599283/50000000000000 : ℝ), (10653183418997/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66819247/125000000 : ℝ)|^4139 ≤ (4350845912091/10000000000000 : ℝ)^3115
        have hw : |(66819247/125000000 : ℝ)|=(66819247/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2262229101/10000000000 : ℝ)|^4139 ≤ (6939403599283/50000000000000 : ℝ)^3115
        have hw : |(-2262229101/10000000000 : ℝ)|=(2262229101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131562579/250000000 : ℝ)|^4139 ≤ (10653183418997/25000000000000 : ℝ)^3115
        have hw : |(131562579/250000000 : ℝ)|=(131562579/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s5_2 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672769773/5000000000 : ℝ)*x 0 + (1315625641/2500000000 : ℝ)*x 1 + (-226223017/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672769773/5000000000 : ℝ)^4139 ≤ (21754228403269/50000000000000 : ℝ)^3115 := by
    have hnat : (2672769773 : ℕ)^4139*50000000000000^3115 ≤ 21754228403269^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672769773 5000000000 21754228403269 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315625641/2500000000 : ℝ)^4139 ≤ (532659090793/1250000000000 : ℝ)^3115 := by
    have hnat : (1315625641 : ℕ)^4139*1250000000000^3115 ≤ 532659090793^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315625641 2500000000 532659090793 1250000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226223017/1000000000 : ℝ)^4139 ≤ (1387881591283/10000000000000 : ℝ)^3115 := by
    have hnat : (226223017 : ℕ)^4139*10000000000000^3115 ≤ 1387881591283^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226223017 1000000000 1387881591283 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672769773/5000000000 : ℝ), (1315625641/2500000000 : ℝ), (-226223017/1000000000 : ℝ)] ![(21754228403269/50000000000000 : ℝ), (532659090793/1250000000000 : ℝ), (1387881591283/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672769773/5000000000 : ℝ)|^4139 ≤ (21754228403269/50000000000000 : ℝ)^3115
        have hw : |(2672769773/5000000000 : ℝ)|=(2672769773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315625641/2500000000 : ℝ)|^4139 ≤ (532659090793/1250000000000 : ℝ)^3115
        have hw : |(1315625641/2500000000 : ℝ)|=(1315625641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226223017/1000000000 : ℝ)|^4139 ≤ (1387881591283/10000000000000 : ℝ)^3115
        have hw : |(-226223017/1000000000 : ℝ)|=(226223017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s5_3 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4372644077/10000000000 : ℝ)*x 0 + (1060720989/2500000000 : ℝ)*x 1 + (2253204173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372644077/10000000000 : ℝ)^4139 ≤ (8328854138097/25000000000000 : ℝ)^3115 := by
    have hnat : (4372644077 : ℕ)^4139*25000000000000^3115 ≤ 8328854138097^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372644077 10000000000 8328854138097 25000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1060720989/2500000000 : ℝ)^4139 ≤ (400102711691/1250000000000 : ℝ)^3115 := by
    have hnat : (1060720989 : ℕ)^4139*1250000000000^3115 ≤ 400102711691^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060720989 2500000000 400102711691 1250000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2253204173/5000000000 : ℝ)^4139 ≤ (1083636453229/3125000000000 : ℝ)^3115 := by
    have hnat : (2253204173 : ℕ)^4139*3125000000000^3115 ≤ 1083636453229^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253204173 5000000000 1083636453229 3125000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372644077/10000000000 : ℝ), (1060720989/2500000000 : ℝ), (2253204173/5000000000 : ℝ)] ![(8328854138097/25000000000000 : ℝ), (400102711691/1250000000000 : ℝ), (1083636453229/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372644077/10000000000 : ℝ)|^4139 ≤ (8328854138097/25000000000000 : ℝ)^3115
        have hw : |(4372644077/10000000000 : ℝ)|=(4372644077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1060720989/2500000000 : ℝ)|^4139 ≤ (400102711691/1250000000000 : ℝ)^3115
        have hw : |(1060720989/2500000000 : ℝ)|=(1060720989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2253204173/5000000000 : ℝ)|^4139 ≤ (1083636453229/3125000000000 : ℝ)^3115
        have hw : |(2253204173/5000000000 : ℝ)|=(2253204173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s5_4 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194240167/10000000000 : ℝ)*x 0 + (526285047/1000000000 : ℝ)*x 1 + (1079221653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194240167/10000000000 : ℝ)^4139 ≤ (1332733221501/10000000000000 : ℝ)^3115 := by
    have hnat : (2194240167 : ℕ)^4139*10000000000000^3115 ≤ 1332733221501^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194240167 10000000000 1332733221501 10000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526285047/1000000000 : ℝ)^4139 ≤ (8523294106463/20000000000000 : ℝ)^3115 := by
    have hnat : (526285047 : ℕ)^4139*20000000000000^3115 ≤ 8523294106463^3115*1000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526285047 1000000000 8523294106463 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079221653/2000000000 : ℝ)^4139 ≤ (22028098618521/50000000000000 : ℝ)^3115 := by
    have hnat : (1079221653 : ℕ)^4139*50000000000000^3115 ≤ 22028098618521^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079221653 2000000000 22028098618521 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194240167/10000000000 : ℝ), (526285047/1000000000 : ℝ), (1079221653/2000000000 : ℝ)] ![(1332733221501/10000000000000 : ℝ), (8523294106463/20000000000000 : ℝ), (22028098618521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194240167/10000000000 : ℝ)|^4139 ≤ (1332733221501/10000000000000 : ℝ)^3115
        have hw : |(-2194240167/10000000000 : ℝ)|=(2194240167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526285047/1000000000 : ℝ)|^4139 ≤ (8523294106463/20000000000000 : ℝ)^3115
        have hw : |(526285047/1000000000 : ℝ)|=(526285047/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079221653/2000000000 : ℝ)|^4139 ≤ (22028098618521/50000000000000 : ℝ)^3115
        have hw : |(1079221653/2000000000 : ℝ)|=(1079221653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s5_5 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327937303/2500000000 : ℝ)*x 0 + (-425724799/2000000000 : ℝ)*x 1 + (5396108267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327937303/2500000000 : ℝ)^4139 ≤ (8628680094447/20000000000000 : ℝ)^3115 := by
    have hnat : (1327937303 : ℕ)^4139*20000000000000^3115 ≤ 8628680094447^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327937303 2500000000 8628680094447 20000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425724799/2000000000 : ℝ)^4139 ≤ (6400201124373/50000000000000 : ℝ)^3115 := by
    have hnat : (425724799 : ℕ)^4139*50000000000000^3115 ≤ 6400201124373^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425724799 2000000000 6400201124373 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396108267/10000000000 : ℝ)^4139 ≤ (44056197258739/100000000000000 : ℝ)^3115 := by
    have hnat : (5396108267 : ℕ)^4139*100000000000000^3115 ≤ 44056197258739^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396108267 10000000000 44056197258739 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327937303/2500000000 : ℝ), (-425724799/2000000000 : ℝ), (5396108267/10000000000 : ℝ)] ![(8628680094447/20000000000000 : ℝ), (6400201124373/50000000000000 : ℝ), (44056197258739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327937303/2500000000 : ℝ)|^4139 ≤ (8628680094447/20000000000000 : ℝ)^3115
        have hw : |(1327937303/2500000000 : ℝ)|=(1327937303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425724799/2000000000 : ℝ)|^4139 ≤ (6400201124373/50000000000000 : ℝ)^3115
        have hw : |(-425724799/2000000000 : ℝ)|=(425724799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396108267/10000000000 : ℝ)|^4139 ≤ (44056197258739/100000000000000 : ℝ)^3115
        have hw : |(5396108267/10000000000 : ℝ)|=(5396108267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s5_6 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655874609/5000000000 : ℝ)*x 0 + (5396108261/10000000000 : ℝ)*x 1 + (-425724799/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655874609/5000000000 : ℝ)^4139 ≤ (43143400536989/100000000000000 : ℝ)^3115 := by
    have hnat : (2655874609 : ℕ)^4139*100000000000000^3115 ≤ 43143400536989^3115*5000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655874609 5000000000 43143400536989 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396108261/10000000000 : ℝ)^4139 ≤ (44056197193649/100000000000000 : ℝ)^3115 := by
    have hnat : (5396108261 : ℕ)^4139*100000000000000^3115 ≤ 44056197193649^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396108261 10000000000 44056197193649 100000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425724799/2000000000 : ℝ)^4139 ≤ (6400201124373/50000000000000 : ℝ)^3115 := by
    have hnat : (425724799 : ℕ)^4139*50000000000000^3115 ≤ 6400201124373^3115*2000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425724799 2000000000 6400201124373 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655874609/5000000000 : ℝ), (5396108261/10000000000 : ℝ), (-425724799/2000000000 : ℝ)] ![(43143400536989/100000000000000 : ℝ), (44056197193649/100000000000000 : ℝ), (6400201124373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655874609/5000000000 : ℝ)|^4139 ≤ (43143400536989/100000000000000 : ℝ)^3115
        have hw : |(2655874609/5000000000 : ℝ)|=(2655874609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396108261/10000000000 : ℝ)|^4139 ≤ (44056197193649/100000000000000 : ℝ)^3115
        have hw : |(5396108261/10000000000 : ℝ)|=(5396108261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425724799/2000000000 : ℝ)|^4139 ≤ (6400201124373/50000000000000 : ℝ)^3115
        have hw : |(-425724799/2000000000 : ℝ)|=(425724799/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1085_s5_7 (p : ℝ) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4372655123/10000000000 : ℝ)*x 0 + (1126430873/2500000000 : ℝ)*x 1 + (4243571319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372655123/10000000000 : ℝ)^4139 ≤ (16657764189313/50000000000000 : ℝ)^3115 := by
    have hnat : (4372655123 : ℕ)^4139*50000000000000^3115 ≤ 16657764189313^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372655123 10000000000 16657764189313 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126430873/2500000000 : ℝ)^4139 ≤ (17334682207659/50000000000000 : ℝ)^3115 := by
    have hnat : (1126430873 : ℕ)^4139*50000000000000^3115 ≤ 17334682207659^3115*2500000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126430873 2500000000 17334682207659 50000000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4243571319/10000000000 : ℝ)^4139 ≤ (4001888399029/12500000000000 : ℝ)^3115 := by
    have hnat : (4243571319 : ℕ)^4139*12500000000000^3115 ≤ 4001888399029^3115*10000000000^4139 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4243571319 10000000000 4001888399029 12500000000000 4139 3115 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4139/1024 : ℝ)) 4139 3115 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372655123/10000000000 : ℝ), (1126430873/2500000000 : ℝ), (4243571319/10000000000 : ℝ)] ![(16657764189313/50000000000000 : ℝ), (17334682207659/50000000000000 : ℝ), (4001888399029/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372655123/10000000000 : ℝ)|^4139 ≤ (16657764189313/50000000000000 : ℝ)^3115
        have hw : |(4372655123/10000000000 : ℝ)|=(4372655123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126430873/2500000000 : ℝ)|^4139 ≤ (17334682207659/50000000000000 : ℝ)^3115
        have hw : |(1126430873/2500000000 : ℝ)|=(1126430873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4243571319/10000000000 : ℝ)|^4139 ≤ (4001888399029/12500000000000 : ℝ)^3115
        have hw : |(4243571319/10000000000 : ℝ)|=(4243571319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1085_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5531/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11229/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7033/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5531/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (89/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5531/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5531/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (89/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5531/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5531/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (89/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5531/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5531/50000 : ℝ) ^ (8277/2048 : ℝ) ≤ (13666269416893371/100000000000000000000 : ℝ) := by
    have hpowers : (5531/50000 : ℝ)^8277 ≤ (13666269416893371/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5531 : ℕ)^8277*100000000000000000000^2048 ≤ 13666269416893371^2048*50000^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5531 50000 13666269416893371 100000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5531/50000 : ℝ)) (X := (13666269416893371/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (89/625 : ℝ) ^ (8277/2048 : ℝ) ≤ (18961702110187051/50000000000000000000 : ℝ) := by
    have hpowers : (89/625 : ℝ)^8277 ≤ (18961702110187051/50000000000000000000 : ℝ)^2048 := by
      have hnat : (89 : ℕ)^8277*50000000000000000000^2048 ≤ 18961702110187051^2048*625^8277 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89 625 18961702110187051 50000000000000000000 8277 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (89/625 : ℝ)) (X := (18961702110187051/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013666269416893371/50000000000000000000 : ℝ) ≤ (1000067622669241/1000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (50013666269416893371/50000000000000000000 : ℝ)^2048 ≤ (1000067622669241/1000000000000000 : ℝ)^8277 := by
      have hnat : (50013666269416893371 : ℕ)^2048*1000000000000000^8277 ≤ 1000067622669241^8277*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013666269416893371 50000000000000000000 1000067622669241 1000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000067622669241/1000000000000000 : ℝ)) (X := (50013666269416893371/50000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051589673637267473/100000000000000000000 : ℝ) ≤ (1000127624921519/1000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (100051589673637267473/100000000000000000000 : ℝ)^2048 ≤ (1000127624921519/1000000000000000 : ℝ)^8277 := by
      have hnat : (100051589673637267473 : ℕ)^2048*1000000000000000^8277 ≤ 1000127624921519^8277*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051589673637267473 100000000000000000000 1000127624921519 1000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000127624921519/1000000000000000 : ℝ)) (X := (100051589673637267473/100000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018961702110187051/25000000000000000000 : ℝ) ≤ (1000187627173797/1000000000000000 : ℝ) ^ (8277/2048 : ℝ) := by
    have hpowers : (25018961702110187051/25000000000000000000 : ℝ)^2048 ≤ (1000187627173797/1000000000000000 : ℝ)^8277 := by
      have hnat : (25018961702110187051 : ℕ)^2048*1000000000000000^8277 ≤ 1000187627173797^8277*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018961702110187051 25000000000000000000 1000187627173797 1000000000000000 2048 8277 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000187627173797/1000000000000000 : ℝ)) (X := (25018961702110187051/25000000000000000000 : ℝ)) (by norm_num) 8277 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13666269416893371/100000000000000000000 : ℝ) ≤ ((1588443707506724713/1589000000000000000 : ℝ)+2*(30001126139/15890000000000 : ℝ)*(5531/50000 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (1588443707506724713/1589000000000000000 : ℝ)+2*(30001126139/15890000000000 : ℝ)*(5531/50000 : ℝ)=(1000067622669241/1000000000000000 : ℝ) by norm_num, show 1+2*(13666269416893371/100000000000000000000 : ℝ)=(50013666269416893371/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18961702110187051/50000000000000000000 : ℝ)+(13666269416893371/100000000000000000000 : ℝ) ≤ ((1588443707506724713/1589000000000000000 : ℝ)+(30001126139/15890000000000 : ℝ)*((89/625 : ℝ)+(5531/50000 : ℝ)))^(8277/2048 : ℝ) := by
    rw [show (1588443707506724713/1589000000000000000 : ℝ)+(30001126139/15890000000000 : ℝ)*((89/625 : ℝ)+(5531/50000 : ℝ))=(1000127624921519/1000000000000000 : ℝ) by norm_num, show 1+(18961702110187051/50000000000000000000 : ℝ)+(13666269416893371/100000000000000000000 : ℝ)=(100051589673637267473/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18961702110187051/50000000000000000000 : ℝ) ≤ ((1588443707506724713/1589000000000000000 : ℝ)+2*(30001126139/15890000000000 : ℝ)*(89/625 : ℝ))^(8277/2048 : ℝ) := by
    rw [show (1588443707506724713/1589000000000000000 : ℝ)+2*(30001126139/15890000000000 : ℝ)*(89/625 : ℝ)=(1000187627173797/1000000000000000 : ℝ) by norm_num, show 1+2*(18961702110187051/50000000000000000000 : ℝ)=(25018961702110187051/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1588443707506724713/1589000000000000000 : ℝ)*(X 1 0+X 2 0)+(30001126139/15890000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (5531/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (1588443707506724713/1589000000000000000 : ℝ)) (alpha := (30001126139/15890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1588443707506724713/1589000000000000000 : ℝ)*(X 0 1+X 2 1)+(30001126139/15890000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (5531/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (1588443707506724713/1589000000000000000 : ℝ)) (alpha := (30001126139/15890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1588443707506724713/1589000000000000000 : ℝ)*(X 0 2+X 1 2)+(30001126139/15890000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8277/2048 : ℝ)) (lo := (5531/50000 : ℝ)) (hi := (89/625 : ℝ)) (c := (1588443707506724713/1589000000000000000 : ℝ)) (alpha := (30001126139/15890000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-438846947/2000000000 : ℝ)*X 0 0+(5396457629/10000000000 : ℝ)*X 0 1+(5262502289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66819247/125000000 : ℝ)*X 1 0+(-2262229101/10000000000 : ℝ)*X 1 1+(131562579/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672769773/5000000000 : ℝ)*X 2 0+(1315625641/2500000000 : ℝ)*X 2 1+(-226223017/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372644077/10000000000 : ℝ)*X 0 0+(1060720989/2500000000 : ℝ)*X 0 1+(2253204173/5000000000 : ℝ)*X 0 2+(4372644077/10000000000 : ℝ)*X 1 0+(1060720989/2500000000 : ℝ)*X 1 1+(2253204173/5000000000 : ℝ)*X 1 2+(4372644077/10000000000 : ℝ)*X 2 0+(1060720989/2500000000 : ℝ)*X 2 1+(2253204173/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2194240167/10000000000 : ℝ)*X 0 0+(526285047/1000000000 : ℝ)*X 0 1+(1079221653/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1327937303/2500000000 : ℝ)*X 1 0+(-425724799/2000000000 : ℝ)*X 1 1+(5396108267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655874609/5000000000 : ℝ)*X 2 0+(5396108261/10000000000 : ℝ)*X 2 1+(-425724799/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372655123/10000000000 : ℝ)*X 0 0+(1126430873/2500000000 : ℝ)*X 0 1+(4243571319/10000000000 : ℝ)*X 0 2+(4372655123/10000000000 : ℝ)*X 1 0+(1126430873/2500000000 : ℝ)*X 1 1+(4243571319/10000000000 : ℝ)*X 1 2+(4372655123/10000000000 : ℝ)*X 2 0+(1126430873/2500000000 : ℝ)*X 2 1+(4243571319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1085_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38395655670298429441239993/9931250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15283773/3125000000000 : ℝ)*(base19) + (79113123/100000000000000 : ℝ)*(base23) + (108191977/100000000000000 : ℝ)*(upper2) + (51327937/20000000000000 : ℝ)*(upper3) + (703753860197063/12500000000000 : ℝ)*(major0) + (703753860197063/12500000000000 : ℝ)*(major1) + (703753860197063/12500000000000 : ℝ)*(major2) + (7465242055230537/100000000000000 : ℝ)*(sp0) + (3732644183555883/50000000000000 : ℝ)*(sp1) + (7465239181640099/100000000000000 : ℝ)*(sp2) + (948685839070711/25000000000000 : ℝ)*(sp3) + (23400480983/50000000000000 : ℝ)*(sp4) + (619942991/1250000000000 : ℝ)*(sp6) + (29421806137/100000000000000 : ℝ)*(sp7) + (189738638904449/5000000000000 : ℝ)*(f.failure) + (3732644428096251/50000000000000 : ℝ)*(f.sum) + (1953646956477/794500000000000000000000000 : ℝ)*base65 + (30374588911205419/19862500000000000000000000000000 : ℝ)*base67 + (39682173627057081/19862500000000000000000000000000 : ℝ)*base70 + (178282144244819581/19862500000000000000000000000000 : ℝ)*base72 + (263741420417/794500000000000000000000000 : ℝ)*base73 + (385777892034780419/19862500000000000000000000000000 : ℝ)*base75 + (85223276341105419/19862500000000000000000000000000 : ℝ)*base77 + (636539056655617919/19862500000000000000000000000000 : ℝ)*base79 + (1981622194179/1589000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (6233943/500000000000000000000 : ℝ)*base90 + (6233943/500000000000000000000 : ℝ)*base92 + (6233943/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (329231588505151529262774741/39725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1513338049/100000000000000 : ℝ)*(base19) + (1655281619/100000000000000 : ℝ)*(base23) + (32924651/20000000000000 : ℝ)*(upper3) + (6070283/10000000000000 : ℝ)*(lower4) + (42245779/25000000000000 : ℝ)*(upper5) + (2829707071730081/50000000000000 : ℝ)*(major0) + (2829707071730081/50000000000000 : ℝ)*(major1) + (2829707071730081/50000000000000 : ℝ)*(major2) + (19969373171/50000000000000 : ℝ)*(sp1) + (21477550809/50000000000000 : ℝ)*(sp2) + (3752125112670061/50000000000000 : ℝ)*(sp4) + (1876052193313933/25000000000000 : ℝ)*(sp5) + (1500841122991377/20000000000000 : ℝ)*(sp6) + (1907288892660629/50000000000000 : ℝ)*(sp7) + (1907288892660629/50000000000000 : ℝ)*(f.failure) + (3752125112670061/50000000000000 : ℝ)*(f.sum) + (2805948139751/397250000000000000000000000 : ℝ)*base66 + (685576242005891753/79450000000000000000000000000000 : ℝ)*base67 + (607956980071691753/79450000000000000000000000000000 : ℝ)*base69 + (350483185395008247/79450000000000000000000000000000 : ℝ)*base72 + (286113411823/158900000000000000000000000 : ℝ)*base73 + (218598618789608247/79450000000000000000000000000000 : ℝ)*base76 + (632391949924691753/79450000000000000000000000000000 : ℝ)*base77 + (929065211254241753/79450000000000000000000000000000 : ℝ)*base79 + (2080103097173/1589000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (19576797/5000000000000000000000 : ℝ)*base89 + (19576797/5000000000000000000000 : ℝ)*base91 + (19576797/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1085_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (89/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5531/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1085_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1085_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1085_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1085_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1085_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8277/2048 : ℝ) ≤ p) (hpb : p ≤ (4139/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148362793/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16679/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2201/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11229/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7033/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1085_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
